/-
Self-contained Lean4Web paste file.
Block 490 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block490

def block490LeftL : Rat := ((36074444196428571639 : Rat) / 50000000000000000000)
def block490LeftR : Rat := ((3608421875000000021 : Rat) / 5000000000000000000)
def block490RightL : Rat := ((86074444196428571639 : Rat) / 50000000000000000000)
def block490RightR : Rat := ((13608421875000000021 : Rat) / 5000000000000000000)

def block490LeftBoxes : List RatBox := [
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((36074444196428571639 : Rat) / 50000000000000000000), R := ((3608421875000000021 : Rat) / 5000000000000000000), D0 := ((3608421875000000021 : Rat) / 5000000000000000000), D1 := ((54799310803571428361 : Rat) / 50000000000000000000), D2 := ((91822305803571428361 : Rat) / 50000000000000000000), D3 := ((23620012633928571411 : Rat) / 12500000000000000000), D4 := ((103150084553571423361 : Rat) / 50000000000000000000), LB := ((1673680546365801 : Rat) / 250000000000000000) }
]

def block490LeftCertificate : Bool :=
  allBoxesValid block490LeftBoxes &&
  coversFromBool block490LeftBoxes block490LeftL block490LeftR

theorem block490LeftCertificate_eq_true :
    block490LeftCertificate = true := by
  native_decide

def block490RightChunk000 : List RatBox := [
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86074444196428571639 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((4799310803571428361 : Rat) / 50000000000000000000), D2 := ((41822305803571428361 : Rat) / 50000000000000000000), D3 := ((11120012633928571411 : Rat) / 12500000000000000000), D4 := ((53150084553571423361 : Rat) / 50000000000000000000), LB := ((36901571354187 : Rat) / 62500000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((39680739732142857283 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((22114886825045707 : Rat) / 100000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((33522361 : Rat) / 16000000), D0 := ((33522361 : Rat) / 16000000), D1 := ((22213797 : Rat) / 80000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((30424990982142857283 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((8996254356101023 : Rat) / 100000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33522361 : Rat) / 16000000), R := ((342628209 : Rat) / 160000000), D0 := ((342628209 : Rat) / 160000000), D1 := ((51832193 : Rat) / 160000000), D2 := ((7404599 : Rat) / 16000000), D3 := ((25797116607142857283 : Rat) / 50000000000000000000), D4 := ((6893430124999999 : Rat) / 10000000000000000), LB := ((6218617974318039 : Rat) / 100000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((342628209 : Rat) / 160000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((66641391 : Rat) / 160000000), D3 := ((23483179419642857283 : Rat) / 50000000000000000000), D4 := ((6430642687499999 : Rat) / 10000000000000000), LB := ((3760562680426419 : Rat) / 250000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((141494043 : Rat) / 64000000), D0 := ((141494043 : Rat) / 64000000), D1 := ((125878183 : Rat) / 320000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((21169242232142857283 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((1835741425131859 : Rat) / 100000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((141494043 : Rat) / 64000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((22213797 : Rat) / 64000000), D3 := ((20012273638392857283 : Rat) / 50000000000000000000), D4 := ((5736461531249999 : Rat) / 10000000000000000), LB := ((35503422693219933 : Rat) / 10000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((1437154227 : Rat) / 640000000), D0 := ((1437154227 : Rat) / 640000000), D1 := ((273970163 : Rat) / 640000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((18855305044642857283 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((9886850644606239 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1437154227 : Rat) / 640000000), R := ((722279413 : Rat) / 320000000), D0 := ((722279413 : Rat) / 320000000), D1 := ((140687381 : Rat) / 320000000), D2 := ((199924173 : Rat) / 640000000), D3 := ((18276820747767857283 : Rat) / 50000000000000000000), D4 := ((5389370953124999 : Rat) / 10000000000000000), LB := ((296233747198103 : Rat) / 62500000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((722279413 : Rat) / 320000000), R := ((58078537 : Rat) / 25600000), D0 := ((58078537 : Rat) / 25600000), D1 := ((288779361 : Rat) / 640000000), D2 := ((96259787 : Rat) / 320000000), D3 := ((17698336450892857283 : Rat) / 50000000000000000000), D4 := ((5273674093749999 : Rat) / 10000000000000000), LB := ((36819735304365747 : Rat) / 100000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((58078537 : Rat) / 25600000), R := ((2911331449 : Rat) / 1280000000), D0 := ((2911331449 : Rat) / 1280000000), D1 := ((584963321 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 25600000), D3 := ((17119852154017857283 : Rat) / 50000000000000000000), D4 := ((5157977234374999 : Rat) / 10000000000000000), LB := ((85306892304627 : Rat) / 15625000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2911331449 : Rat) / 1280000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((362825351 : Rat) / 1280000000), D3 := ((16830610005580357283 : Rat) / 50000000000000000000), D4 := ((5100128804687499 : Rat) / 10000000000000000), LB := ((7764690168770523 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((2926140647 : Rat) / 1280000000), D0 := ((2926140647 : Rat) / 1280000000), D1 := ((599772519 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((16541367857142857283 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((2508707531662567 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2926140647 : Rat) / 1280000000), R := ((1466772623 : Rat) / 640000000), D0 := ((1466772623 : Rat) / 640000000), D1 := ((303588559 : Rat) / 640000000), D2 := ((348016153 : Rat) / 1280000000), D3 := ((16252125708705357283 : Rat) / 50000000000000000000), D4 := ((4984431945312499 : Rat) / 10000000000000000), LB := ((13410435918391299 : Rat) / 10000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1466772623 : Rat) / 640000000), R := ((588189969 : Rat) / 256000000), D0 := ((588189969 : Rat) / 256000000), D1 := ((614581717 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 640000000), D3 := ((15962883560267857283 : Rat) / 50000000000000000000), D4 := ((4926583515624999 : Rat) / 10000000000000000), LB := ((1527848897788453 : Rat) / 4000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((588189969 : Rat) / 256000000), R := ((5889304289 : Rat) / 2560000000), D0 := ((5889304289 : Rat) / 2560000000), D1 := ((1236568033 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 256000000), D3 := ((15673641411830357283 : Rat) / 50000000000000000000), D4 := ((4868735085937499 : Rat) / 10000000000000000), LB := ((7607892277911317 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5889304289 : Rat) / 2560000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((659009311 : Rat) / 2560000000), D3 := ((15529020337611607283 : Rat) / 50000000000000000000), D4 := ((4839810871093749 : Rat) / 10000000000000000), LB := ((3491600304683779 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((5904113487 : Rat) / 2560000000), D0 := ((5904113487 : Rat) / 2560000000), D1 := ((1251377231 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((15384399263392857283 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((129343089323357 : Rat) / 40000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5904113487 : Rat) / 2560000000), R := ((2955759043 : Rat) / 1280000000), D0 := ((2955759043 : Rat) / 1280000000), D1 := ((125878183 : Rat) / 256000000), D2 := ((644200113 : Rat) / 2560000000), D3 := ((15239778189174107283 : Rat) / 50000000000000000000), D4 := ((4781962441406249 : Rat) / 10000000000000000), LB := ((6060662145537729 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2955759043 : Rat) / 1280000000), R := ((1183784537 : Rat) / 512000000), D0 := ((1183784537 : Rat) / 512000000), D1 := ((1266186429 : Rat) / 2560000000), D2 := ((318397757 : Rat) / 1280000000), D3 := ((15095157114955357283 : Rat) / 50000000000000000000), D4 := ((4753038226562499 : Rat) / 10000000000000000), LB := ((1441169187314439 : Rat) / 500000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1183784537 : Rat) / 512000000), R := ((1481581821 : Rat) / 640000000), D0 := ((1481581821 : Rat) / 640000000), D1 := ((318397757 : Rat) / 640000000), D2 := ((125878183 : Rat) / 512000000), D3 := ((14950536040736607283 : Rat) / 50000000000000000000), D4 := ((4724114011718749 : Rat) / 10000000000000000), LB := ((2790098728433981 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1481581821 : Rat) / 640000000), R := ((5933731883 : Rat) / 2560000000), D0 := ((5933731883 : Rat) / 2560000000), D1 := ((1280995627 : Rat) / 2560000000), D2 := ((155496579 : Rat) / 640000000), D3 := ((14805914966517857283 : Rat) / 50000000000000000000), D4 := ((4695189796874999 : Rat) / 10000000000000000), LB := ((2754135436766423 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5933731883 : Rat) / 2560000000), R := ((2970568241 : Rat) / 1280000000), D0 := ((2970568241 : Rat) / 1280000000), D1 := ((644200113 : Rat) / 1280000000), D2 := ((614581717 : Rat) / 2560000000), D3 := ((14661293892299107283 : Rat) / 50000000000000000000), D4 := ((4666265582031249 : Rat) / 10000000000000000), LB := ((5549992456509209 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2970568241 : Rat) / 1280000000), R := ((5948541081 : Rat) / 2560000000), D0 := ((5948541081 : Rat) / 2560000000), D1 := ((51832193 : Rat) / 102400000), D2 := ((303588559 : Rat) / 1280000000), D3 := ((14516672818080357283 : Rat) / 50000000000000000000), D4 := ((4637341367187499 : Rat) / 10000000000000000), LB := ((5706508024436327 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5948541081 : Rat) / 2560000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((599772519 : Rat) / 2560000000), D3 := ((14372051743861607283 : Rat) / 50000000000000000000), D4 := ((4608417152343749 : Rat) / 10000000000000000), LB := ((149475383850153 : Rat) / 50000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((5963350279 : Rat) / 2560000000), D0 := ((5963350279 : Rat) / 2560000000), D1 := ((1310614023 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((14227430669642857283 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((3184382934437263 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5963350279 : Rat) / 2560000000), R := ((2985377439 : Rat) / 1280000000), D0 := ((2985377439 : Rat) / 1280000000), D1 := ((659009311 : Rat) / 1280000000), D2 := ((584963321 : Rat) / 2560000000), D3 := ((14082809595424107283 : Rat) / 50000000000000000000), D4 := ((4550568722656249 : Rat) / 10000000000000000), LB := ((6877066426053291 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2985377439 : Rat) / 1280000000), R := ((5978159477 : Rat) / 2560000000), D0 := ((5978159477 : Rat) / 2560000000), D1 := ((1325423221 : Rat) / 2560000000), D2 := ((288779361 : Rat) / 1280000000), D3 := ((13938188521205357283 : Rat) / 50000000000000000000), D4 := ((4521644507812499 : Rat) / 10000000000000000), LB := ((7505281205454059 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5978159477 : Rat) / 2560000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((570154123 : Rat) / 2560000000), D3 := ((13793567446986607283 : Rat) / 50000000000000000000), D4 := ((4492720292968749 : Rat) / 10000000000000000), LB := ((8254833708603651 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((3000186637 : Rat) / 1280000000), D0 := ((3000186637 : Rat) / 1280000000), D1 := ((673818509 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((13648946372767857283 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((6404589339018447 : Rat) / 10000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3000186637 : Rat) / 1280000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((273970163 : Rat) / 1280000000), D3 := ((13359704224330357283 : Rat) / 50000000000000000000), D4 := ((4405947648437499 : Rat) / 10000000000000000), LB := ((17325412858865963 : Rat) / 10000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((13070462075892857283 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((30793506979324113 : Rat) / 10000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((12781219927455357283 : Rat) / 50000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((4688076005877631 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((12491977779017857283 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((13133043601173379 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((12202735630580357283 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((4361580288071383 : Rat) / 500000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((11913493482142857283 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((746718914700141 : Rat) / 200000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((11335009185267857283 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((1927401142963181 : Rat) / 200000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((10756524888392857283 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((25487012304451703 : Rat) / 10000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((9599556294642857283 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((21593732302507697 : Rat) / 1000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((8442587700892857283 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((4731667700370959 : Rat) / 100000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((7285619107142857283 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((11705992878266569 : Rat) / 2000000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((130554494732142857283 : Rat) / 50000000000000000000), D0 := ((130554494732142857283 : Rat) / 50000000000000000000), D1 := ((39680739732142857283 : Rat) / 50000000000000000000), D2 := ((2657744732142857283 : Rat) / 50000000000000000000), D3 := ((2657744732142857283 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1807049386134907 : Rat) / 5000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((130554494732142857283 : Rat) / 50000000000000000000), R := ((266638713482142857493 : Rat) / 100000000000000000000), D0 := ((266638713482142857493 : Rat) / 100000000000000000000), D1 := ((84891203482142857493 : Rat) / 100000000000000000000), D2 := ((10845213482142857493 : Rat) / 100000000000000000000), D3 := ((5529724017857142927 : Rat) / 100000000000000000000), D4 := ((8670034017857137717 : Rat) / 50000000000000000000), LB := ((1501985024019587 : Rat) / 5000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((266638713482142857493 : Rat) / 100000000000000000000), R := ((538807150982142857913 : Rat) / 200000000000000000000), D0 := ((538807150982142857913 : Rat) / 200000000000000000000), D1 := ((175312130982142857913 : Rat) / 200000000000000000000), D2 := ((27220150982142857913 : Rat) / 200000000000000000000), D3 := ((16589172053571428781 : Rat) / 200000000000000000000), D4 := ((11810344017857132507 : Rat) / 100000000000000000000), LB := ((6304866926859451 : Rat) / 50000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((538807150982142857913 : Rat) / 200000000000000000000), R := ((1083144025982142858753 : Rat) / 400000000000000000000), D0 := ((1083144025982142858753 : Rat) / 400000000000000000000), D1 := ((356153985982142858753 : Rat) / 400000000000000000000), D2 := ((59970025982142858753 : Rat) / 400000000000000000000), D3 := ((38708068125000000489 : Rat) / 400000000000000000000), D4 := ((18090964017857122087 : Rat) / 200000000000000000000), LB := ((30379762481189433 : Rat) / 500000000000000000) },
  { w1 := ((9758723592056191 : Rat) / 20000000000000000), w2 := (0 : Rat), w3 := ((1978964639277941 : Rat) / 5000000000000000), w4 := ((15798965040075823 : Rat) / 500000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((130554494732142857283 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1083144025982142858753 : Rat) / 400000000000000000000), R := ((13608421875000000021 : Rat) / 5000000000000000000), D0 := ((13608421875000000021 : Rat) / 5000000000000000000), D1 := ((4521046375000000021 : Rat) / 5000000000000000000), D2 := ((818746875000000021 : Rat) / 5000000000000000000), D3 := ((5529724017857142927 : Rat) / 50000000000000000000), D4 := ((30652204017857101247 : Rat) / 400000000000000000000), LB := ((5395670824488441 : Rat) / 10000000000000000000) }
]

def block490RightChunk000L : Rat := ((86074444196428571639 : Rat) / 50000000000000000000)
def block490RightChunk000R : Rat := ((13608421875000000021 : Rat) / 5000000000000000000)

def block490RightChunk000Certificate : Bool :=
  allBoxesValid block490RightChunk000 &&
  coversFromBool block490RightChunk000 block490RightChunk000L block490RightChunk000R

theorem block490RightChunk000Certificate_eq_true :
    block490RightChunk000Certificate = true := by
  native_decide

def block490RightChainCertificate : Bool :=
  decide (
    block490RightL = ((86074444196428571639 : Rat) / 50000000000000000000) /\
    ((13608421875000000021 : Rat) / 5000000000000000000) = block490RightR)

theorem block490RightChainCertificate_eq_true :
    block490RightChainCertificate = true := by
  native_decide

def block490LeftBoxCount : Nat := boxCount block490LeftBoxes
def block490RightBoxCount : Nat := 46

def block490_rational_certificate : Prop :=
    block490LeftCertificate = true /\
    block490RightChainCertificate = true /\
    block490RightChunk000Certificate = true

theorem block490_rational_certificate_proof :
    block490_rational_certificate := by
  exact ⟨block490LeftCertificate_eq_true, block490RightChainCertificate_eq_true, block490RightChunk000Certificate_eq_true⟩

end Block490
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block490

open Set

def block490W1 : Rat := ((9758723592056191 : Rat) / 20000000000000000)
def block490W2 : Rat := (0 : Rat)
def block490W3 : Rat := ((1978964639277941 : Rat) / 5000000000000000)
def block490W4 : Rat := ((15798965040075823 : Rat) / 500000000000000000)
def block490S1 : Rat := ((18174751 : Rat) / 10000000)
def block490S2 : Rat := ((511587 : Rat) / 200000)
def block490S3 : Rat := ((130554494732142857283 : Rat) / 50000000000000000000)
def block490S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block490V (y : ℝ) : ℝ :=
  ratPotential block490W1 block490W2 block490W3 block490W4 block490S1 block490S2 block490S3 block490S4 y

def block490LeftParamsCertificate : Bool :=
  allBoxesSameParams block490LeftBoxes block490W1 block490W2 block490W3 block490W4 block490S1 block490S2 block490S3 block490S4

theorem block490LeftParamsCertificate_eq_true :
    block490LeftParamsCertificate = true := by
  native_decide

theorem block490_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block490LeftL : ℝ) (block490LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block490S1 : ℝ))
    (hy2ne : y ≠ (block490S2 : ℝ))
    (hy3ne : y ≠ (block490S3 : ℝ))
    (hy4ne : y ≠ (block490S4 : ℝ)) :
    0 < block490V y := by
  have hcert := block490LeftCertificate_eq_true
  unfold block490LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block490LeftBoxes) (lo := block490LeftL) (hi := block490LeftR)
    (w1 := block490W1) (w2 := block490W2) (w3 := block490W3) (w4 := block490W4)
    (s1 := block490S1) (s2 := block490S2) (s3 := block490S3) (s4 := block490S4)
    hboxes hcover block490LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block490RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block490RightChunk000 block490W1 block490W2 block490W3 block490W4 block490S1 block490S2 block490S3 block490S4

theorem block490RightChunk000ParamsCertificate_eq_true :
    block490RightChunk000ParamsCertificate = true := by
  native_decide

theorem block490_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block490RightChunk000L : ℝ) (block490RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block490S1 : ℝ))
    (hy2ne : y ≠ (block490S2 : ℝ))
    (hy3ne : y ≠ (block490S3 : ℝ))
    (hy4ne : y ≠ (block490S4 : ℝ)) :
    0 < block490V y := by
  have hcert := block490RightChunk000Certificate_eq_true
  unfold block490RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block490RightChunk000) (lo := block490RightChunk000L) (hi := block490RightChunk000R)
    (w1 := block490W1) (w2 := block490W2) (w3 := block490W3) (w4 := block490W4)
    (s1 := block490S1) (s2 := block490S2) (s3 := block490S3) (s4 := block490S4)
    hboxes hcover block490RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block490_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block490RightL : ℝ) (block490RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block490S1 : ℝ))
    (hy2ne : y ≠ (block490S2 : ℝ))
    (hy3ne : y ≠ (block490S3 : ℝ))
    (hy4ne : y ≠ (block490S4 : ℝ)) :
    0 < block490V y := by
  have hL : (block490RightChunk000L : ℝ) = (block490RightL : ℝ) := by
    norm_num [block490RightChunk000L, block490RightL]
  have hR : (block490RightChunk000R : ℝ) = (block490RightR : ℝ) := by
    norm_num [block490RightChunk000R, block490RightR]
  have hyc : y ∈ Icc (block490RightChunk000L : ℝ) (block490RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block490_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block490_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block490LeftL : ℝ) (block490LeftR : ℝ) →
    y ≠ 0 → y ≠ (block490S1 : ℝ) → y ≠ (block490S2 : ℝ) →
    y ≠ (block490S3 : ℝ) → y ≠ (block490S4 : ℝ) → 0 < block490V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block490RightL : ℝ) (block490RightR : ℝ) →
    y ≠ 0 → y ≠ (block490S1 : ℝ) → y ≠ (block490S2 : ℝ) →
    y ≠ (block490S3 : ℝ) → y ≠ (block490S4 : ℝ) → 0 < block490V y)

theorem block490_reallog_certificate_proof :
    block490_reallog_certificate := by
  exact ⟨block490_left_V_pos, block490_right_V_pos⟩

end Block490
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block490.block490V
#check Erdos1038Lean.M1817475.Block490.block490_left_V_pos
#check Erdos1038Lean.M1817475.Block490.block490_right_V_pos
#check Erdos1038Lean.M1817475.Block490.block490_reallog_certificate_proof
