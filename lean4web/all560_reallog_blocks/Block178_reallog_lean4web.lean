/-
Self-contained Lean4Web paste file.
Block 178 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block178

def block178LeftL : Rat := ((39124104910714285791 : Rat) / 50000000000000000000)
def block178LeftR : Rat := ((19566939732142857181 : Rat) / 25000000000000000000)
def block178RightL : Rat := ((89124104910714285791 : Rat) / 50000000000000000000)
def block178RightR : Rat := ((69566939732142857181 : Rat) / 25000000000000000000)

def block178LeftBoxes : List RatBox := [
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((39124104910714285791 : Rat) / 50000000000000000000), R := ((19566939732142857181 : Rat) / 25000000000000000000), D0 := ((19566939732142857181 : Rat) / 25000000000000000000), D1 := ((51749650089285714209 : Rat) / 50000000000000000000), D2 := ((88772645089285714209 : Rat) / 50000000000000000000), D3 := ((48461844464285714197 : Rat) / 25000000000000000000), D4 := ((100100423839285709209 : Rat) / 50000000000000000000), LB := ((12860011323787973 : Rat) / 10000000000000000000) }
]

def block178LeftCertificate : Bool :=
  allBoxesValid block178LeftBoxes &&
  coversFromBool block178LeftBoxes block178LeftL block178LeftR

theorem block178LeftCertificate_eq_true :
    block178LeftCertificate = true := by
  native_decide

def block178RightChunk000 : List RatBox := [
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((89124104910714285791 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1749650089285714209 : Rat) / 50000000000000000000), D2 := ((38772645089285714209 : Rat) / 50000000000000000000), D3 := ((23461844464285714197 : Rat) / 25000000000000000000), D4 := ((50100423839285709209 : Rat) / 50000000000000000000), LB := ((5427516632323079 : Rat) / 1000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((2550998608434149 : Rat) / 2500000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((34995805485540177 : Rat) / 100000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((725118824651553 : Rat) / 5000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((4043757914698043 : Rat) / 50000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((6266154945144117 : Rat) / 100000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((1274787259370043 : Rat) / 50000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1264124713483833 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((228242040749429 : Rat) / 40000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((2416240740392199 : Rat) / 250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((1326707930186799 : Rat) / 250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((2749419882715931 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((9309847339542321 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((1921476483813557 : Rat) / 625000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((1618532425213981 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((5836301149085843 : Rat) / 20000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((669503238910714285533 : Rat) / 256000000000000000000), D0 := ((669503238910714285533 : Rat) / 256000000000000000000), D1 := ((204229613310714285533 : Rat) / 256000000000000000000), D2 := ((14671878910714285533 : Rat) / 256000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((4894666867036157 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((669503238910714285533 : Rat) / 256000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((135307327732142855471 : Rat) / 1280000000000000000000), D4 := ((43326348289285688867 : Rat) / 256000000000000000000), LB := ((2372259059972813 : Rat) / 1250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((1383654144392149 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((9055582285880381 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((1160571296165841 : Rat) / 2500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((15100038991681941 : Rat) / 250000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((6712964685553571426537 : Rat) / 2560000000000000000000), D0 := ((6712964685553571426537 : Rat) / 2560000000000000000000), D1 := ((2060228429553571426537 : Rat) / 2560000000000000000000), D2 := ((164651085553571426537 : Rat) / 2560000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((13565510904217093 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6712964685553571426537 : Rat) / 2560000000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((50536471803571427947 : Rat) / 512000000000000000000), D4 := ((415331186446428317463 : Rat) / 2560000000000000000000), LB := ((2374367192343907 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((6716225103089285712211 : Rat) / 2560000000000000000000), D0 := ((6716225103089285712211 : Rat) / 2560000000000000000000), D1 := ((2063488847089285712211 : Rat) / 2560000000000000000000), D2 := ((167911503089285712211 : Rat) / 2560000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((1284603693118419 : Rat) / 1250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6716225103089285712211 : Rat) / 2560000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((249421941482142854061 : Rat) / 2560000000000000000000), D4 := ((412070768910714031789 : Rat) / 2560000000000000000000), LB := ((274422754399763 : Rat) / 312500000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((7386988097050073 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((3047143065360719 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((245225992645981 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((4773510388791577 : Rat) / 12500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((5676585097684761 : Rat) / 20000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((392827237051141 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((2395052025131461 : Rat) / 20000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((26983630738205977 : Rat) / 500000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((538536966910714285533 : Rat) / 204800000000000000000), D0 := ((538536966910714285533 : Rat) / 204800000000000000000), D1 := ((166318066430714285533 : Rat) / 204800000000000000000), D2 := ((14671878910714285533 : Rat) / 204800000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((4117253926986253 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((538536966910714285533 : Rat) / 204800000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((467869916374999994219 : Rat) / 5120000000000000000000), D4 := ((31726702849285693987 : Rat) / 204800000000000000000), LB := ((1999828697333561 : Rat) / 2500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((13466684590303571423999 : Rat) / 5120000000000000000000), D0 := ((13466684590303571423999 : Rat) / 5120000000000000000000), D1 := ((4161212078303571423999 : Rat) / 5120000000000000000000), D2 := ((370057390303571423999 : Rat) / 5120000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((3896048202038649 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13466684590303571423999 : Rat) / 5120000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((92921899767857141709 : Rat) / 1024000000000000000000), D4 := ((789907153696428064001 : Rat) / 5120000000000000000000), LB := ((951626780261311 : Rat) / 1250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((13469945007839285709673 : Rat) / 5120000000000000000000), D0 := ((13469945007839285709673 : Rat) / 5120000000000000000000), D1 := ((4164472495839285709673 : Rat) / 5120000000000000000000), D2 := ((373317807839285709673 : Rat) / 5120000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((7462231502357031 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13469945007839285709673 : Rat) / 5120000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((461349081303571422871 : Rat) / 5120000000000000000000), D4 := ((786646736160713778327 : Rat) / 5120000000000000000000), LB := ((366995653083263 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((13473205425374999995347 : Rat) / 5120000000000000000000), D0 := ((13473205425374999995347 : Rat) / 5120000000000000000000), D1 := ((4167732913374999995347 : Rat) / 5120000000000000000000), D2 := ((376578225374999995347 : Rat) / 5120000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((3623112748868257 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13473205425374999995347 : Rat) / 5120000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((458088663767857137197 : Rat) / 5120000000000000000000), D4 := ((783386318624999492653 : Rat) / 5120000000000000000000), LB := ((1795334278156327 : Rat) / 2500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((13476465842910714281021 : Rat) / 5120000000000000000000), D0 := ((13476465842910714281021 : Rat) / 5120000000000000000000), D1 := ((4170993330910714281021 : Rat) / 5120000000000000000000), D2 := ((379838642910714281021 : Rat) / 5120000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((7145417956741507 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13476465842910714281021 : Rat) / 5120000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((454828246232142851523 : Rat) / 5120000000000000000000), D4 := ((780125901089285206979 : Rat) / 5120000000000000000000), LB := ((1427727970617021 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((2695945252089285713339 : Rat) / 1024000000000000000000), D0 := ((2695945252089285713339 : Rat) / 1024000000000000000000), D1 := ((834850749689285713339 : Rat) / 1024000000000000000000), D2 := ((76619812089285713339 : Rat) / 1024000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((1432235284419603 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2695945252089285713339 : Rat) / 1024000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((451567828696428565849 : Rat) / 5120000000000000000000), D4 := ((155373096710714184261 : Rat) / 1024000000000000000000), LB := ((1803300776689401 : Rat) / 2500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((13482986677982142852369 : Rat) / 5120000000000000000000), D0 := ((13482986677982142852369 : Rat) / 5120000000000000000000), D1 := ((4177514165982142852369 : Rat) / 5120000000000000000000), D2 := ((386359477982142852369 : Rat) / 5120000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((455931074895919 : Rat) / 625000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13482986677982142852369 : Rat) / 5120000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((17932296446428571207 : Rat) / 204800000000000000000), D4 := ((773605066017856635631 : Rat) / 5120000000000000000000), LB := ((3703218931198349 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((13486247095517857138043 : Rat) / 5120000000000000000000), D0 := ((13486247095517857138043 : Rat) / 5120000000000000000000), D1 := ((4180774583517857138043 : Rat) / 5120000000000000000000), D2 := ((389619895517857138043 : Rat) / 5120000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((7548006165468413 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13486247095517857138043 : Rat) / 5120000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((445046993624999994501 : Rat) / 5120000000000000000000), D4 := ((770344648482142349957 : Rat) / 5120000000000000000000), LB := ((3859892551015681 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((13489507513053571423717 : Rat) / 5120000000000000000000), D0 := ((13489507513053571423717 : Rat) / 5120000000000000000000), D1 := ((4184035001053571423717 : Rat) / 5120000000000000000000), D2 := ((392880313053571423717 : Rat) / 5120000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((396097981104529 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13489507513053571423717 : Rat) / 5120000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((441786576089285708827 : Rat) / 5120000000000000000000), D4 := ((767084230946428064283 : Rat) / 5120000000000000000000), LB := ((2038679164800411 : Rat) / 2500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((22745010703068003 : Rat) / 1000000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((8533110884498263 : Rat) / 100000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((16045682798815353 : Rat) / 100000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((6207021844949201 : Rat) / 25000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((3489654640962403 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((462676433722331 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((5895833433932907 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((3649297963706777 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((8836825377147861 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((657021007854381 : Rat) / 625000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((770436535390967 : Rat) / 625000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((1428267046094861 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((8190669155612451 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((1499559311969427 : Rat) / 6250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((7352108513672961 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((6454927622538409 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((1909028216176889 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((323900420498853 : Rat) / 125000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((1499100583607707 : Rat) / 12500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((9159529301882019 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((9586101612598097 : Rat) / 2500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((3073722844025767 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((3046009467701713 : Rat) / 1250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((4432043312922379 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((888268514495183 : Rat) / 200000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((1297066851545653 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((9497695529907677 : Rat) / 100000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((547277260982142856917 : Rat) / 200000000000000000000), D0 := ((547277260982142856917 : Rat) / 200000000000000000000), D1 := ((183782240982142856917 : Rat) / 200000000000000000000), D2 := ((35690260982142856917 : Rat) / 200000000000000000000), D3 := ((3086085625000000177 : Rat) / 200000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((6705624878214547 : Rat) / 50000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((547277260982142856917 : Rat) / 200000000000000000000), R := ((275181673303571428547 : Rat) / 100000000000000000000), D0 := ((275181673303571428547 : Rat) / 100000000000000000000), D1 := ((93434163303571428547 : Rat) / 100000000000000000000), D2 := ((19388173303571428547 : Rat) / 100000000000000000000), D3 := ((3086085625000000177 : Rat) / 100000000000000000000), D4 := ((9620854017857123083 : Rat) / 200000000000000000000), LB := ((12506639835763833 : Rat) / 2000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275181673303571428547 : Rat) / 100000000000000000000), R := ((2204539472053571428553 : Rat) / 800000000000000000000), D0 := ((2204539472053571428553 : Rat) / 800000000000000000000), D1 := ((750559392053571428553 : Rat) / 800000000000000000000), D2 := ((158191472053571428553 : Rat) / 800000000000000000000), D3 := ((27774770625000001593 : Rat) / 800000000000000000000), D4 := ((3267384196428561453 : Rat) / 100000000000000000000), LB := ((7481491426011483 : Rat) / 500000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2204539472053571428553 : Rat) / 800000000000000000000), R := ((220762555767857142873 : Rat) / 80000000000000000000), D0 := ((220762555767857142873 : Rat) / 80000000000000000000), D1 := ((75364547767857142873 : Rat) / 80000000000000000000), D2 := ((16127755767857142873 : Rat) / 80000000000000000000), D3 := ((3086085625000000177 : Rat) / 80000000000000000000), D4 := ((23052987946428491447 : Rat) / 800000000000000000000), LB := ((7818846640797461 : Rat) / 25000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220762555767857142873 : Rat) / 80000000000000000000), R := ((4418337200982142857637 : Rat) / 1600000000000000000000), D0 := ((4418337200982142857637 : Rat) / 1600000000000000000000), D1 := ((1510377040982142857637 : Rat) / 1600000000000000000000), D2 := ((325641200982142857637 : Rat) / 1600000000000000000000), D3 := ((64807798125000003717 : Rat) / 1600000000000000000000), D4 := ((1996690232142849127 : Rat) / 80000000000000000000), LB := ((7904375921861939 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4418337200982142857637 : Rat) / 1600000000000000000000), R := ((8839760487589285715451 : Rat) / 3200000000000000000000), D0 := ((8839760487589285715451 : Rat) / 3200000000000000000000), D1 := ((3023840167589285715451 : Rat) / 3200000000000000000000), D2 := ((654368487589285715451 : Rat) / 3200000000000000000000), D3 := ((132701681875000007611 : Rat) / 3200000000000000000000), D4 := ((36847719017856982363 : Rat) / 1600000000000000000000), LB := ((16024904456642397 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8839760487589285715451 : Rat) / 3200000000000000000000), R := ((2210711643303571428907 : Rat) / 800000000000000000000), D0 := ((2210711643303571428907 : Rat) / 800000000000000000000), D1 := ((756731563303571428907 : Rat) / 800000000000000000000), D2 := ((164363643303571428907 : Rat) / 800000000000000000000), D3 := ((33946941875000001947 : Rat) / 800000000000000000000), D4 := ((70609352410713964549 : Rat) / 3200000000000000000000), LB := ((12430336483103543 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2210711643303571428907 : Rat) / 800000000000000000000), R := ((17688779232053571431433 : Rat) / 6400000000000000000000), D0 := ((17688779232053571431433 : Rat) / 6400000000000000000000), D1 := ((6056938592053571431433 : Rat) / 6400000000000000000000), D2 := ((1317995232053571431433 : Rat) / 6400000000000000000000), D3 := ((274661620625000015753 : Rat) / 6400000000000000000000), D4 := ((16880816696428491093 : Rat) / 800000000000000000000), LB := ((12873786559993161 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17688779232053571431433 : Rat) / 6400000000000000000000), R := ((1769186531767857143161 : Rat) / 640000000000000000000), D0 := ((1769186531767857143161 : Rat) / 640000000000000000000), D1 := ((606002467767857143161 : Rat) / 640000000000000000000), D2 := ((132108131767857143161 : Rat) / 640000000000000000000), D3 := ((27774770625000001593 : Rat) / 640000000000000000000), D4 := ((131960447946427928567 : Rat) / 6400000000000000000000), LB := ((1819429205007883 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1769186531767857143161 : Rat) / 640000000000000000000), R := ((17694951403303571431787 : Rat) / 6400000000000000000000), D0 := ((17694951403303571431787 : Rat) / 6400000000000000000000), D1 := ((6063110763303571431787 : Rat) / 6400000000000000000000), D2 := ((1324167403303571431787 : Rat) / 6400000000000000000000), D3 := ((280833791875000016107 : Rat) / 6400000000000000000000), D4 := ((12887436232142792839 : Rat) / 640000000000000000000), LB := ((11393817188893873 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17694951403303571431787 : Rat) / 6400000000000000000000), R := ((4424509372232142857991 : Rat) / 1600000000000000000000), D0 := ((4424509372232142857991 : Rat) / 1600000000000000000000), D1 := ((1516549212232142857991 : Rat) / 1600000000000000000000), D2 := ((331813372232142857991 : Rat) / 1600000000000000000000), D3 := ((70979969375000004071 : Rat) / 1600000000000000000000), D4 := ((125788276696427928213 : Rat) / 6400000000000000000000), LB := ((5367409418390867 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4424509372232142857991 : Rat) / 1600000000000000000000), R := ((17701123574553571432141 : Rat) / 6400000000000000000000), D0 := ((17701123574553571432141 : Rat) / 6400000000000000000000), D1 := ((6069282934553571432141 : Rat) / 6400000000000000000000), D2 := ((1330339574553571432141 : Rat) / 6400000000000000000000), D3 := ((287005963125000016461 : Rat) / 6400000000000000000000), D4 := ((30675547767856982009 : Rat) / 1600000000000000000000), LB := ((6920457858355933 : Rat) / 500000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17701123574553571432141 : Rat) / 6400000000000000000000), R := ((35405333234732142864459 : Rat) / 12800000000000000000000), D0 := ((35405333234732142864459 : Rat) / 12800000000000000000000), D1 := ((12141651954732142864459 : Rat) / 12800000000000000000000), D2 := ((2663765234732142864459 : Rat) / 12800000000000000000000), D3 := ((577098011875000033099 : Rat) / 12800000000000000000000), D4 := ((119616105446427927859 : Rat) / 6400000000000000000000), LB := ((5181507966058041 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35405333234732142864459 : Rat) / 12800000000000000000000), R := ((8852104830089285716159 : Rat) / 3200000000000000000000), D0 := ((8852104830089285716159 : Rat) / 3200000000000000000000), D1 := ((3036184510089285716159 : Rat) / 3200000000000000000000), D2 := ((666712830089285716159 : Rat) / 3200000000000000000000), D3 := ((145046024375000008319 : Rat) / 3200000000000000000000), D4 := ((236146125267855855541 : Rat) / 12800000000000000000000), LB := ((1053411202415061 : Rat) / 1250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8852104830089285716159 : Rat) / 3200000000000000000000), R := ((35411505405982142864813 : Rat) / 12800000000000000000000), D0 := ((35411505405982142864813 : Rat) / 12800000000000000000000), D1 := ((12147824125982142864813 : Rat) / 12800000000000000000000), D2 := ((2669937405982142864813 : Rat) / 12800000000000000000000), D3 := ((583270183125000033453 : Rat) / 12800000000000000000000), D4 := ((58265009910713963841 : Rat) / 3200000000000000000000), LB := ((268342975159519 : Rat) / 400000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35411505405982142864813 : Rat) / 12800000000000000000000), R := ((3541459149160714286499 : Rat) / 1280000000000000000000), D0 := ((3541459149160714286499 : Rat) / 1280000000000000000000), D1 := ((1215091021160714286499 : Rat) / 1280000000000000000000), D2 := ((267302349160714286499 : Rat) / 1280000000000000000000), D3 := ((58635626875000003363 : Rat) / 1280000000000000000000), D4 := ((229973954017855855187 : Rat) / 12800000000000000000000), LB := ((162837546605777 : Rat) / 312500000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3541459149160714286499 : Rat) / 1280000000000000000000), R := ((35417677577232142865167 : Rat) / 12800000000000000000000), D0 := ((35417677577232142865167 : Rat) / 12800000000000000000000), D1 := ((12153996297232142865167 : Rat) / 12800000000000000000000), D2 := ((2676109577232142865167 : Rat) / 12800000000000000000000), D3 := ((589442354375000033807 : Rat) / 12800000000000000000000), D4 := ((22688786839285585501 : Rat) / 1280000000000000000000), LB := ((39380898731306013 : Rat) / 100000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35417677577232142865167 : Rat) / 12800000000000000000000), R := ((553449432232142857271 : Rat) / 200000000000000000000), D0 := ((553449432232142857271 : Rat) / 200000000000000000000), D1 := ((189954412232142857271 : Rat) / 200000000000000000000), D2 := ((41862432232142857271 : Rat) / 200000000000000000000), D3 := ((9258256875000000531 : Rat) / 200000000000000000000), D4 := ((223801782767855854833 : Rat) / 12800000000000000000000), LB := ((1809222268114169 : Rat) / 6250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553449432232142857271 : Rat) / 200000000000000000000), R := ((35423849748482142865521 : Rat) / 12800000000000000000000), D0 := ((35423849748482142865521 : Rat) / 12800000000000000000000), D1 := ((12160168468482142865521 : Rat) / 12800000000000000000000), D2 := ((2682281748482142865521 : Rat) / 12800000000000000000000), D3 := ((595614525625000034161 : Rat) / 12800000000000000000000), D4 := ((3448682767857122729 : Rat) / 200000000000000000000), LB := ((4170644529203349 : Rat) / 20000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35423849748482142865521 : Rat) / 12800000000000000000000), R := ((17713467917053571432849 : Rat) / 6400000000000000000000), D0 := ((17713467917053571432849 : Rat) / 6400000000000000000000), D1 := ((6081627277053571432849 : Rat) / 6400000000000000000000), D2 := ((1342683917053571432849 : Rat) / 6400000000000000000000), D3 := ((299350305625000017169 : Rat) / 6400000000000000000000), D4 := ((217629611517855854479 : Rat) / 12800000000000000000000), LB := ((473291129206993 : Rat) / 3125000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17713467917053571432849 : Rat) / 6400000000000000000000), R := ((283440175357857142927 : Rat) / 102400000000000000000), D0 := ((283440175357857142927 : Rat) / 102400000000000000000), D1 := ((97330725117857142927 : Rat) / 102400000000000000000), D2 := ((21507631357857142927 : Rat) / 102400000000000000000), D3 := ((120357339375000006903 : Rat) / 2560000000000000000000), D4 := ((107271762946427927151 : Rat) / 6400000000000000000000), LB := ((2374711069643709 : Rat) / 20000000000000000000) }
]

def block178RightChunk000L : Rat := ((89124104910714285791 : Rat) / 50000000000000000000)
def block178RightChunk000R : Rat := ((283440175357857142927 : Rat) / 102400000000000000000)

def block178RightChunk000Certificate : Bool :=
  allBoxesValid block178RightChunk000 &&
  coversFromBool block178RightChunk000 block178RightChunk000L block178RightChunk000R

theorem block178RightChunk000Certificate_eq_true :
    block178RightChunk000Certificate = true := by
  native_decide

def block178RightChunk001 : List RatBox := [
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((283440175357857142927 : Rat) / 102400000000000000000), R := ((8858277001339285716513 : Rat) / 3200000000000000000000), D0 := ((8858277001339285716513 : Rat) / 3200000000000000000000), D1 := ((3042356681339285716513 : Rat) / 3200000000000000000000), D2 := ((672885001339285716513 : Rat) / 3200000000000000000000), D3 := ((151218195625000008673 : Rat) / 3200000000000000000000), D4 := ((1691659522142846833 : Rat) / 102400000000000000000), LB := ((443603378297297 : Rat) / 4000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8858277001339285716513 : Rat) / 3200000000000000000000), R := ((35436194090982142866229 : Rat) / 12800000000000000000000), D0 := ((35436194090982142866229 : Rat) / 12800000000000000000000), D1 := ((12172512810982142866229 : Rat) / 12800000000000000000000), D2 := ((2694626090982142866229 : Rat) / 12800000000000000000000), D3 := ((607958868125000034869 : Rat) / 12800000000000000000000), D4 := ((52092838660713963487 : Rat) / 3200000000000000000000), LB := ((12849607553994113 : Rat) / 100000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35436194090982142866229 : Rat) / 12800000000000000000000), R := ((17719640088303571433203 : Rat) / 6400000000000000000000), D0 := ((17719640088303571433203 : Rat) / 6400000000000000000000), D1 := ((6087799448303571433203 : Rat) / 6400000000000000000000), D2 := ((1348856088303571433203 : Rat) / 6400000000000000000000), D3 := ((305522476875000017523 : Rat) / 6400000000000000000000), D4 := ((205285269017855853771 : Rat) / 12800000000000000000000), LB := ((1075595798064391 : Rat) / 6250000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17719640088303571433203 : Rat) / 6400000000000000000000), R := ((35442366262232142866583 : Rat) / 12800000000000000000000), D0 := ((35442366262232142866583 : Rat) / 12800000000000000000000), D1 := ((12178684982232142866583 : Rat) / 12800000000000000000000), D2 := ((2700798262232142866583 : Rat) / 12800000000000000000000), D3 := ((614131039375000035223 : Rat) / 12800000000000000000000), D4 := ((101099591696427926797 : Rat) / 6400000000000000000000), LB := ((24230126984653433 : Rat) / 100000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35442366262232142866583 : Rat) / 12800000000000000000000), R := ((886136308696428571669 : Rat) / 320000000000000000000), D0 := ((886136308696428571669 : Rat) / 320000000000000000000), D1 := ((304544276696428571669 : Rat) / 320000000000000000000), D2 := ((67597108696428571669 : Rat) / 320000000000000000000), D3 := ((3086085625000000177 : Rat) / 64000000000000000000), D4 := ((199113097767855853417 : Rat) / 12800000000000000000000), LB := ((339746820403497 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((886136308696428571669 : Rat) / 320000000000000000000), R := ((35448538433482142866937 : Rat) / 12800000000000000000000), D0 := ((35448538433482142866937 : Rat) / 12800000000000000000000), D1 := ((12184857153482142866937 : Rat) / 12800000000000000000000), D2 := ((2706970433482142866937 : Rat) / 12800000000000000000000), D3 := ((620303210625000035577 : Rat) / 12800000000000000000000), D4 := ((4900675303571396331 : Rat) / 320000000000000000000), LB := ((46509693419327647 : Rat) / 100000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35448538433482142866937 : Rat) / 12800000000000000000000), R := ((17725812259553571433557 : Rat) / 6400000000000000000000), D0 := ((17725812259553571433557 : Rat) / 6400000000000000000000), D1 := ((6093971619553571433557 : Rat) / 6400000000000000000000), D2 := ((1355028259553571433557 : Rat) / 6400000000000000000000), D3 := ((311694648125000017877 : Rat) / 6400000000000000000000), D4 := ((192940926517855853063 : Rat) / 12800000000000000000000), LB := ((6190505249769607 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17725812259553571433557 : Rat) / 6400000000000000000000), R := ((35454710604732142867291 : Rat) / 12800000000000000000000), D0 := ((35454710604732142867291 : Rat) / 12800000000000000000000), D1 := ((12191029324732142867291 : Rat) / 12800000000000000000000), D2 := ((2713142604732142867291 : Rat) / 12800000000000000000000), D3 := ((626475381875000035931 : Rat) / 12800000000000000000000), D4 := ((94927420446427926443 : Rat) / 6400000000000000000000), LB := ((8023425354500291 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35454710604732142867291 : Rat) / 12800000000000000000000), R := ((8864449172589285716867 : Rat) / 3200000000000000000000), D0 := ((8864449172589285716867 : Rat) / 3200000000000000000000), D1 := ((3048528852589285716867 : Rat) / 3200000000000000000000), D2 := ((679057172589285716867 : Rat) / 3200000000000000000000), D3 := ((157390366875000009027 : Rat) / 3200000000000000000000), D4 := ((186768755267855852709 : Rat) / 12800000000000000000000), LB := ((5078730839014889 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8864449172589285716867 : Rat) / 3200000000000000000000), R := ((7092176555196428573529 : Rat) / 2560000000000000000000), D0 := ((7092176555196428573529 : Rat) / 2560000000000000000000), D1 := ((2439440299196428573529 : Rat) / 2560000000000000000000), D2 := ((543862955196428573529 : Rat) / 2560000000000000000000), D3 := ((126529510625000007257 : Rat) / 2560000000000000000000), D4 := ((45920667410713963133 : Rat) / 3200000000000000000000), LB := ((6300376446198297 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7092176555196428573529 : Rat) / 2560000000000000000000), R := ((17731984430803571433911 : Rat) / 6400000000000000000000), D0 := ((17731984430803571433911 : Rat) / 6400000000000000000000), D1 := ((6100143790803571433911 : Rat) / 6400000000000000000000), D2 := ((1361200430803571433911 : Rat) / 6400000000000000000000), D3 := ((317866819375000018231 : Rat) / 6400000000000000000000), D4 := ((36119316803571170471 : Rat) / 2560000000000000000000), LB := ((7680935141053391 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17731984430803571433911 : Rat) / 6400000000000000000000), R := ((2216883814553571429261 : Rat) / 800000000000000000000), D0 := ((2216883814553571429261 : Rat) / 800000000000000000000), D1 := ((762903734553571429261 : Rat) / 800000000000000000000), D2 := ((170535814553571429261 : Rat) / 800000000000000000000), D3 := ((40119113125000002301 : Rat) / 800000000000000000000), D4 := ((88755249196427926089 : Rat) / 6400000000000000000000), LB := ((2365287649659653 : Rat) / 5000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2216883814553571429261 : Rat) / 800000000000000000000), R := ((3547631320410714286853 : Rat) / 1280000000000000000000), D0 := ((3547631320410714286853 : Rat) / 1280000000000000000000), D1 := ((1221263192410714286853 : Rat) / 1280000000000000000000), D2 := ((273474520410714286853 : Rat) / 1280000000000000000000), D3 := ((64807798125000003717 : Rat) / 1280000000000000000000), D4 := ((10708645446428490739 : Rat) / 800000000000000000000), LB := ((12007523036734469 : Rat) / 10000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3547631320410714286853 : Rat) / 1280000000000000000000), R := ((8870621343839285717221 : Rat) / 3200000000000000000000), D0 := ((8870621343839285717221 : Rat) / 3200000000000000000000), D1 := ((3054701023839285717221 : Rat) / 3200000000000000000000), D2 := ((685229343839285717221 : Rat) / 3200000000000000000000), D3 := ((163562538125000009381 : Rat) / 3200000000000000000000), D4 := ((16516615589285585147 : Rat) / 1280000000000000000000), LB := ((258896250995351 : Rat) / 125000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8870621343839285717221 : Rat) / 3200000000000000000000), R := ((4436853714732142858699 : Rat) / 1600000000000000000000), D0 := ((4436853714732142858699 : Rat) / 1600000000000000000000), D1 := ((1528893554732142858699 : Rat) / 1600000000000000000000), D2 := ((344157714732142858699 : Rat) / 1600000000000000000000), D3 := ((83324311875000004779 : Rat) / 1600000000000000000000), D4 := ((39748496160713962779 : Rat) / 3200000000000000000000), LB := ((1279717885910997 : Rat) / 3125000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4436853714732142858699 : Rat) / 1600000000000000000000), R := ((355071740603571428703 : Rat) / 128000000000000000000), D0 := ((355071740603571428703 : Rat) / 128000000000000000000), D1 := ((122434927803571428703 : Rat) / 128000000000000000000), D2 := ((27656060603571428703 : Rat) / 128000000000000000000), D3 := ((33946941875000001947 : Rat) / 640000000000000000000), D4 := ((18331205267856981301 : Rat) / 1600000000000000000000), LB := ((2982987797821801 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((355071740603571428703 : Rat) / 128000000000000000000), R := ((1109984950089285714719 : Rat) / 400000000000000000000), D0 := ((1109984950089285714719 : Rat) / 400000000000000000000), D1 := ((382994910089285714719 : Rat) / 400000000000000000000), D2 := ((86810950089285714719 : Rat) / 400000000000000000000), D3 := ((21602599375000001239 : Rat) / 400000000000000000000), D4 := ((1343052996428558497 : Rat) / 128000000000000000000), LB := ((63048420755909 : Rat) / 10000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109984950089285714719 : Rat) / 400000000000000000000), R := ((4443025885982142859053 : Rat) / 1600000000000000000000), D0 := ((4443025885982142859053 : Rat) / 1600000000000000000000), D1 := ((1535065725982142859053 : Rat) / 1600000000000000000000), D2 := ((350329885982142859053 : Rat) / 1600000000000000000000), D3 := ((89496483125000005133 : Rat) / 1600000000000000000000), D4 := ((3811279910714245281 : Rat) / 400000000000000000000), LB := ((5350061731099753 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4443025885982142859053 : Rat) / 1600000000000000000000), R := ((444611197160714285923 : Rat) / 160000000000000000000), D0 := ((444611197160714285923 : Rat) / 160000000000000000000), D1 := ((153815181160714285923 : Rat) / 160000000000000000000), D2 := ((35341597160714285923 : Rat) / 160000000000000000000), D3 := ((9258256875000000531 : Rat) / 160000000000000000000), D4 := ((12159034017856980947 : Rat) / 1600000000000000000000), LB := ((17180384133422433 : Rat) / 1000000000000000000) },
  { w1 := ((896944818900707 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := ((8624953731371919 : Rat) / 50000000000000000), w4 := ((4888770839424123 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((444611197160714285923 : Rat) / 160000000000000000000), R := ((69566939732142857181 : Rat) / 25000000000000000000), D0 := ((69566939732142857181 : Rat) / 25000000000000000000), D1 := ((24130062232142857181 : Rat) / 25000000000000000000), D2 := ((5618564732142857181 : Rat) / 25000000000000000000), D3 := ((3086085625000000177 : Rat) / 50000000000000000000), D4 := ((907294839285698077 : Rat) / 160000000000000000000), LB := ((2552212475313831 : Rat) / 100000000000000000) }
]

def block178RightChunk001L : Rat := ((283440175357857142927 : Rat) / 102400000000000000000)
def block178RightChunk001R : Rat := ((69566939732142857181 : Rat) / 25000000000000000000)

def block178RightChunk001Certificate : Bool :=
  allBoxesValid block178RightChunk001 &&
  coversFromBool block178RightChunk001 block178RightChunk001L block178RightChunk001R

theorem block178RightChunk001Certificate_eq_true :
    block178RightChunk001Certificate = true := by
  native_decide

def block178RightChainCertificate : Bool :=
  decide (
    block178RightL = ((89124104910714285791 : Rat) / 50000000000000000000) /\
    ((283440175357857142927 : Rat) / 102400000000000000000) = ((283440175357857142927 : Rat) / 102400000000000000000) /\
    ((69566939732142857181 : Rat) / 25000000000000000000) = block178RightR)

theorem block178RightChainCertificate_eq_true :
    block178RightChainCertificate = true := by
  native_decide

def block178LeftBoxCount : Nat := boxCount block178LeftBoxes
def block178RightBoxCount : Nat := 120

def block178_rational_certificate : Prop :=
    block178LeftCertificate = true /\
    block178RightChainCertificate = true /\
    block178RightChunk000Certificate = true /\
    block178RightChunk001Certificate = true

theorem block178_rational_certificate_proof :
    block178_rational_certificate := by
  exact ⟨block178LeftCertificate_eq_true, block178RightChainCertificate_eq_true, block178RightChunk000Certificate_eq_true, block178RightChunk001Certificate_eq_true⟩

end Block178
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block178

open Set

def block178W1 : Rat := ((896944818900707 : Rat) / 500000000000000)
def block178W2 : Rat := (0 : Rat)
def block178W3 : Rat := ((8624953731371919 : Rat) / 50000000000000000)
def block178W4 : Rat := ((4888770839424123 : Rat) / 50000000000000000)
def block178S1 : Rat := ((18174751 : Rat) / 10000000)
def block178S2 : Rat := ((511587 : Rat) / 200000)
def block178S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block178S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block178V (y : ℝ) : ℝ :=
  ratPotential block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4 y

def block178LeftParamsCertificate : Bool :=
  allBoxesSameParams block178LeftBoxes block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4

theorem block178LeftParamsCertificate_eq_true :
    block178LeftParamsCertificate = true := by
  native_decide

theorem block178_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178LeftL : ℝ) (block178LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  have hcert := block178LeftCertificate_eq_true
  unfold block178LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block178LeftBoxes) (lo := block178LeftL) (hi := block178LeftR)
    (w1 := block178W1) (w2 := block178W2) (w3 := block178W3) (w4 := block178W4)
    (s1 := block178S1) (s2 := block178S2) (s3 := block178S3) (s4 := block178S4)
    hboxes hcover block178LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block178RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block178RightChunk000 block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4

theorem block178RightChunk000ParamsCertificate_eq_true :
    block178RightChunk000ParamsCertificate = true := by
  native_decide

theorem block178_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178RightChunk000L : ℝ) (block178RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  have hcert := block178RightChunk000Certificate_eq_true
  unfold block178RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block178RightChunk000) (lo := block178RightChunk000L) (hi := block178RightChunk000R)
    (w1 := block178W1) (w2 := block178W2) (w3 := block178W3) (w4 := block178W4)
    (s1 := block178S1) (s2 := block178S2) (s3 := block178S3) (s4 := block178S4)
    hboxes hcover block178RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block178RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block178RightChunk001 block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4

theorem block178RightChunk001ParamsCertificate_eq_true :
    block178RightChunk001ParamsCertificate = true := by
  native_decide

theorem block178_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178RightChunk001L : ℝ) (block178RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  have hcert := block178RightChunk001Certificate_eq_true
  unfold block178RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block178RightChunk001) (lo := block178RightChunk001L) (hi := block178RightChunk001R)
    (w1 := block178W1) (w2 := block178W2) (w3 := block178W3) (w4 := block178W4)
    (s1 := block178S1) (s2 := block178S2) (s3 := block178S3) (s4 := block178S4)
    hboxes hcover block178RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block178_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178RightL : ℝ) (block178RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  by_cases h0 : y ≤ (block178RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block178RightChunk000L : ℝ) (block178RightChunk000R : ℝ) := by
      have hL : (block178RightChunk000L : ℝ) = (block178RightL : ℝ) := by
        norm_num [block178RightChunk000L, block178RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block178_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block178RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block178RightChunk001L : ℝ) = (block178RightChunk000R : ℝ) := by
      norm_num [block178RightChunk001L, block178RightChunk000R]
    have hR : (block178RightChunk001R : ℝ) = (block178RightR : ℝ) := by
      norm_num [block178RightChunk001R, block178RightR]
    have hyc : y ∈ Icc (block178RightChunk001L : ℝ) (block178RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block178_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block178_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block178LeftL : ℝ) (block178LeftR : ℝ) →
    y ≠ 0 → y ≠ (block178S1 : ℝ) → y ≠ (block178S2 : ℝ) →
    y ≠ (block178S3 : ℝ) → y ≠ (block178S4 : ℝ) → 0 < block178V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block178RightL : ℝ) (block178RightR : ℝ) →
    y ≠ 0 → y ≠ (block178S1 : ℝ) → y ≠ (block178S2 : ℝ) →
    y ≠ (block178S3 : ℝ) → y ≠ (block178S4 : ℝ) → 0 < block178V y)

theorem block178_reallog_certificate_proof :
    block178_reallog_certificate := by
  exact ⟨block178_left_V_pos, block178_right_V_pos⟩

end Block178
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block178.block178V
#check Erdos1038Lean.M1817475.Block178.block178_left_V_pos
#check Erdos1038Lean.M1817475.Block178.block178_right_V_pos
#check Erdos1038Lean.M1817475.Block178.block178_reallog_certificate_proof
