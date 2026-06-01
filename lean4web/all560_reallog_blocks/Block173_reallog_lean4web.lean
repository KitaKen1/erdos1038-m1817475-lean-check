/-
Self-contained Lean4Web paste file.
Block 173 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block173

def block173LeftL : Rat := ((19586488839285714323 : Rat) / 25000000000000000000)
def block173LeftR : Rat := ((39182752232142857217 : Rat) / 50000000000000000000)
def block173RightL : Rat := ((44586488839285714323 : Rat) / 25000000000000000000)
def block173RightR : Rat := ((139182752232142857217 : Rat) / 50000000000000000000)

def block173LeftBoxes : List RatBox := [
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19586488839285714323 : Rat) / 25000000000000000000), R := ((39182752232142857217 : Rat) / 50000000000000000000), D0 := ((39182752232142857217 : Rat) / 50000000000000000000), D1 := ((25850388660714285677 : Rat) / 25000000000000000000), D2 := ((44361886160714285677 : Rat) / 25000000000000000000), D3 := ((96874816160714285539 : Rat) / 50000000000000000000), D4 := ((50025775535714283177 : Rat) / 25000000000000000000), LB := ((3520216475705329 : Rat) / 2000000000000000000) }
]

def block173LeftCertificate : Bool :=
  allBoxesValid block173LeftBoxes &&
  coversFromBool block173LeftBoxes block173LeftL block173LeftR

theorem block173LeftCertificate_eq_true :
    block173LeftCertificate = true := by
  native_decide

def block173RightChunk000 : List RatBox := [
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((44586488839285714323 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((850388660714285677 : Rat) / 25000000000000000000), D2 := ((19361886160714285677 : Rat) / 25000000000000000000), D3 := ((46874816160714285539 : Rat) / 50000000000000000000), D4 := ((25025775535714283177 : Rat) / 25000000000000000000), LB := ((69255655943633 : Rat) / 12500000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((519198786798061 : Rat) / 500000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((17998128404768693 : Rat) / 50000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((3792781979916579 : Rat) / 25000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((1718233865093943 : Rat) / 20000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((20712195303776437 : Rat) / 100000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((3998324122483993 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((249876772741223 : Rat) / 31250000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((5859798317059739 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((3589883399073013 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((7658584692281159 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((3107870066112059 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((4540273713607407 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((29886801930937013 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((3913210119564567 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((27470925786249323 : Rat) / 100000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((12449736728361027 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((19620440541200657 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((14706196501836633 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((10163995246537383 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((3000680425246649 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((11130505176651373 : Rat) / 50000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((778052080816799 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((280204588542049 : Rat) / 200000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((1570185973351311 : Rat) / 1250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((11215920644278843 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((3989861448637 : Rat) / 4000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((1767766916741853 : Rat) / 2000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((7809634227254059 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((6888246689053801 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((12151780351079 : Rat) / 20000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((1343451903382531 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((23916336618218237 : Rat) / 50000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((1076390929232729 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((788403603207033 : Rat) / 2000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((3693979001709591 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((7125647571655791 : Rat) / 20000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((17749793060459207 : Rat) / 50000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((4571024607000207 : Rat) / 12500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((4856092540665713 : Rat) / 12500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((42356203912616297 : Rat) / 100000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((2355295068213331 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((5311348237190539 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((6039494251548483 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((6896663358026689 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((3942263713345301 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((4502398065615587 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((5129609051979789 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((232991642718261 : Rat) / 200000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((13177718423960927 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((148454998674033 : Rat) / 100000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((1665484341631579 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((4481396133118043 : Rat) / 20000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((6607723135444721 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((2893382537774991 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((857780592218027 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((5843086066558631 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((7560761967097679 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((236175337621573 : Rat) / 62500000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((3410507403843327 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((8097632618602399 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((677614222250017 : Rat) / 125000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((15201061936941651 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((7664917547464373 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((1415308180719707 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((4160711758127711 : Rat) / 50000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((1808550930093703 : Rat) / 20000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((136831533437499999943 : Rat) / 50000000000000000000), D0 := ((136831533437499999943 : Rat) / 50000000000000000000), D1 := ((45957778437499999943 : Rat) / 50000000000000000000), D2 := ((8934783437499999943 : Rat) / 50000000000000000000), D3 := ((391869799107142879 : Rat) / 25000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((6288834316429251 : Rat) / 50000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((136831533437499999943 : Rat) / 50000000000000000000), R := ((137615273035714285701 : Rat) / 50000000000000000000), D0 := ((137615273035714285701 : Rat) / 50000000000000000000), D1 := ((46741518035714285701 : Rat) / 50000000000000000000), D2 := ((9718523035714285701 : Rat) / 50000000000000000000), D3 := ((391869799107142879 : Rat) / 12500000000000000000), D4 := ((2392995312499995057 : Rat) / 50000000000000000000), LB := ((4918047893223143 : Rat) / 20000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((137615273035714285701 : Rat) / 50000000000000000000), R := ((275622415870535714281 : Rat) / 100000000000000000000), D0 := ((275622415870535714281 : Rat) / 100000000000000000000), D1 := ((93874905870535714281 : Rat) / 100000000000000000000), D2 := ((19828915870535714281 : Rat) / 100000000000000000000), D3 := ((3526828191964285911 : Rat) / 100000000000000000000), D4 := ((1609255714285709299 : Rat) / 50000000000000000000), LB := ((1365262445273803 : Rat) / 125000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275622415870535714281 : Rat) / 100000000000000000000), R := ((551636701540178571441 : Rat) / 200000000000000000000), D0 := ((551636701540178571441 : Rat) / 200000000000000000000), D1 := ((188141681540178571441 : Rat) / 200000000000000000000), D2 := ((40049701540178571441 : Rat) / 200000000000000000000), D3 := ((7445526183035714701 : Rat) / 200000000000000000000), D4 := ((2826641629464275719 : Rat) / 100000000000000000000), LB := ((10240698993291109 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((551636701540178571441 : Rat) / 200000000000000000000), R := ((6900357141741071429 : Rat) / 2500000000000000000), D0 := ((6900357141741071429 : Rat) / 2500000000000000000), D1 := ((2356669391741071429 : Rat) / 2500000000000000000), D2 := ((505519641741071429 : Rat) / 2500000000000000000), D3 := ((391869799107142879 : Rat) / 10000000000000000000), D4 := ((5261413459821408559 : Rat) / 200000000000000000000), LB := ((2121780641267529 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6900357141741071429 : Rat) / 2500000000000000000), R := ((1104449012477678571519 : Rat) / 400000000000000000000), D0 := ((1104449012477678571519 : Rat) / 400000000000000000000), D1 := ((377458972477678571519 : Rat) / 400000000000000000000), D2 := ((81275012477678571519 : Rat) / 400000000000000000000), D3 := ((16066661763392858039 : Rat) / 400000000000000000000), D4 := ((60869295758928321 : Rat) / 2500000000000000000), LB := ((2777165636959733 : Rat) / 500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1104449012477678571519 : Rat) / 400000000000000000000), R := ((552420441138392857199 : Rat) / 200000000000000000000), D0 := ((552420441138392857199 : Rat) / 200000000000000000000), D1 := ((188925421138392857199 : Rat) / 200000000000000000000), D2 := ((40833441138392857199 : Rat) / 200000000000000000000), D3 := ((8229265781250000459 : Rat) / 200000000000000000000), D4 := ((9347217522321388481 : Rat) / 400000000000000000000), LB := ((1335243901643679 : Rat) / 400000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552420441138392857199 : Rat) / 200000000000000000000), R := ((1105232752075892857277 : Rat) / 400000000000000000000), D0 := ((1105232752075892857277 : Rat) / 400000000000000000000), D1 := ((378242712075892857277 : Rat) / 400000000000000000000), D2 := ((82058752075892857277 : Rat) / 400000000000000000000), D3 := ((16850401361607143797 : Rat) / 400000000000000000000), D4 := ((4477673861607122801 : Rat) / 200000000000000000000), LB := ((3489583852696737 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1105232752075892857277 : Rat) / 400000000000000000000), R := ((2210857373950892857433 : Rat) / 800000000000000000000), D0 := ((2210857373950892857433 : Rat) / 800000000000000000000), D1 := ((756877293950892857433 : Rat) / 800000000000000000000), D2 := ((164509373950892857433 : Rat) / 800000000000000000000), D3 := ((34092672522321430473 : Rat) / 800000000000000000000), D4 := ((8563477924107102723 : Rat) / 400000000000000000000), LB := ((697786263103059 : Rat) / 250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2210857373950892857433 : Rat) / 800000000000000000000), R := ((276406155468750000039 : Rat) / 100000000000000000000), D0 := ((276406155468750000039 : Rat) / 100000000000000000000), D1 := ((94658645468750000039 : Rat) / 100000000000000000000), D2 := ((20612655468750000039 : Rat) / 100000000000000000000), D3 := ((4310567790178571669 : Rat) / 100000000000000000000), D4 := ((16735086049107062567 : Rat) / 800000000000000000000), LB := ((410281583957639 : Rat) / 200000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276406155468750000039 : Rat) / 100000000000000000000), R := ((2211641113549107143191 : Rat) / 800000000000000000000), D0 := ((2211641113549107143191 : Rat) / 800000000000000000000), D1 := ((757661033549107143191 : Rat) / 800000000000000000000), D2 := ((165293113549107143191 : Rat) / 800000000000000000000), D3 := ((34876412120535716231 : Rat) / 800000000000000000000), D4 := ((2042902031249989961 : Rat) / 100000000000000000000), LB := ((13888717391106753 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2211641113549107143191 : Rat) / 800000000000000000000), R := ((221203298334821428607 : Rat) / 80000000000000000000), D0 := ((221203298334821428607 : Rat) / 80000000000000000000), D1 := ((75805290334821428607 : Rat) / 80000000000000000000), D2 := ((16568498334821428607 : Rat) / 80000000000000000000), D3 := ((3526828191964285911 : Rat) / 80000000000000000000), D4 := ((15951346450892776809 : Rat) / 800000000000000000000), LB := ((1007132507003447 : Rat) / 1250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221203298334821428607 : Rat) / 80000000000000000000), R := ((2212424853147321428949 : Rat) / 800000000000000000000), D0 := ((2212424853147321428949 : Rat) / 800000000000000000000), D1 := ((758444773147321428949 : Rat) / 800000000000000000000), D2 := ((166076853147321428949 : Rat) / 800000000000000000000), D3 := ((35660151718750001989 : Rat) / 800000000000000000000), D4 := ((1555947665178563393 : Rat) / 80000000000000000000), LB := ((6085891626923523 : Rat) / 20000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2212424853147321428949 : Rat) / 800000000000000000000), R := ((4425241576093750000777 : Rat) / 1600000000000000000000), D0 := ((4425241576093750000777 : Rat) / 1600000000000000000000), D1 := ((1517281416093750000777 : Rat) / 1600000000000000000000), D2 := ((332545576093750000777 : Rat) / 1600000000000000000000), D3 := ((71712173236607146857 : Rat) / 1600000000000000000000), D4 := ((15167606852678491051 : Rat) / 800000000000000000000), LB := ((1709317943484473 : Rat) / 1250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4425241576093750000777 : Rat) / 1600000000000000000000), R := ((553204180736607142957 : Rat) / 200000000000000000000), D0 := ((553204180736607142957 : Rat) / 200000000000000000000), D1 := ((189709160736607142957 : Rat) / 200000000000000000000), D2 := ((41617180736607142957 : Rat) / 200000000000000000000), D3 := ((9013005379464286217 : Rat) / 200000000000000000000), D4 := ((29943343906249839223 : Rat) / 1600000000000000000000), LB := ((1186326408809113 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553204180736607142957 : Rat) / 200000000000000000000), R := ((885205063138392857307 : Rat) / 320000000000000000000), D0 := ((885205063138392857307 : Rat) / 320000000000000000000), D1 := ((303613031138392857307 : Rat) / 320000000000000000000), D2 := ((66665863138392857307 : Rat) / 320000000000000000000), D3 := ((14499182566964286523 : Rat) / 320000000000000000000), D4 := ((3693934263392837043 : Rat) / 200000000000000000000), LB := ((1027444344379791 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((885205063138392857307 : Rat) / 320000000000000000000), R := ((2213208592745535714707 : Rat) / 800000000000000000000), D0 := ((2213208592745535714707 : Rat) / 800000000000000000000), D1 := ((759228512745535714707 : Rat) / 800000000000000000000), D2 := ((166860592745535714707 : Rat) / 800000000000000000000), D3 := ((36443891316964287747 : Rat) / 800000000000000000000), D4 := ((5831920861607110693 : Rat) / 320000000000000000000), LB := ((1114013197606803 : Rat) / 1250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2213208592745535714707 : Rat) / 800000000000000000000), R := ((4426809055290178572293 : Rat) / 1600000000000000000000), D0 := ((4426809055290178572293 : Rat) / 1600000000000000000000), D1 := ((1518848895290178572293 : Rat) / 1600000000000000000000), D2 := ((334113055290178572293 : Rat) / 1600000000000000000000), D3 := ((73279652433035718373 : Rat) / 1600000000000000000000), D4 := ((14383867254464205293 : Rat) / 800000000000000000000), LB := ((486279235044941 : Rat) / 625000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4426809055290178572293 : Rat) / 1600000000000000000000), R := ((1106800231272321428793 : Rat) / 400000000000000000000), D0 := ((1106800231272321428793 : Rat) / 400000000000000000000), D1 := ((379810191272321428793 : Rat) / 400000000000000000000), D2 := ((83626231272321428793 : Rat) / 400000000000000000000), D3 := ((18417880558035715313 : Rat) / 400000000000000000000), D4 := ((28375864709821267707 : Rat) / 1600000000000000000000), LB := ((3441975188865909 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106800231272321428793 : Rat) / 400000000000000000000), R := ((4427592794888392858051 : Rat) / 1600000000000000000000), D0 := ((4427592794888392858051 : Rat) / 1600000000000000000000), D1 := ((1519632634888392858051 : Rat) / 1600000000000000000000), D2 := ((334896794888392858051 : Rat) / 1600000000000000000000), D3 := ((74063392031250004131 : Rat) / 1600000000000000000000), D4 := ((6995998727678531207 : Rat) / 400000000000000000000), LB := ((6227187481133711 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4427592794888392858051 : Rat) / 1600000000000000000000), R := ((442798466468750000093 : Rat) / 160000000000000000000), D0 := ((442798466468750000093 : Rat) / 160000000000000000000), D1 := ((152002450468750000093 : Rat) / 160000000000000000000), D2 := ((33528866468750000093 : Rat) / 160000000000000000000), D3 := ((7445526183035714701 : Rat) / 160000000000000000000), D4 := ((27592125111606981949 : Rat) / 1600000000000000000000), LB := ((5815038036500741 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((442798466468750000093 : Rat) / 160000000000000000000), R := ((4428376534486607143809 : Rat) / 1600000000000000000000), D0 := ((4428376534486607143809 : Rat) / 1600000000000000000000), D1 := ((1520416374486607143809 : Rat) / 1600000000000000000000), D2 := ((335680534486607143809 : Rat) / 1600000000000000000000), D3 := ((74847131629464289889 : Rat) / 1600000000000000000000), D4 := ((2720025531249983907 : Rat) / 160000000000000000000), LB := ((1130519597249413 : Rat) / 2000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4428376534486607143809 : Rat) / 1600000000000000000000), R := ((138399012633928571459 : Rat) / 50000000000000000000), D0 := ((138399012633928571459 : Rat) / 50000000000000000000), D1 := ((47525257633928571459 : Rat) / 50000000000000000000), D2 := ((10502262633928571459 : Rat) / 50000000000000000000), D3 := ((1175609397321428637 : Rat) / 25000000000000000000), D4 := ((26808385513392696191 : Rat) / 1600000000000000000000), LB := ((5745213174531139 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138399012633928571459 : Rat) / 50000000000000000000), R := ((4429160274084821429567 : Rat) / 1600000000000000000000), D0 := ((4429160274084821429567 : Rat) / 1600000000000000000000), D1 := ((1521200114084821429567 : Rat) / 1600000000000000000000), D2 := ((336464274084821429567 : Rat) / 1600000000000000000000), D3 := ((75630871227678575647 : Rat) / 1600000000000000000000), D4 := ((825516116071423541 : Rat) / 50000000000000000000), LB := ((6098493207981059 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4429160274084821429567 : Rat) / 1600000000000000000000), R := ((2214776071941964286223 : Rat) / 800000000000000000000), D0 := ((2214776071941964286223 : Rat) / 800000000000000000000), D1 := ((760795991941964286223 : Rat) / 800000000000000000000), D2 := ((168428071941964286223 : Rat) / 800000000000000000000), D3 := ((38011370513392859263 : Rat) / 800000000000000000000), D4 := ((26024645915178410433 : Rat) / 1600000000000000000000), LB := ((6718326330083513 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214776071941964286223 : Rat) / 800000000000000000000), R := ((177197760547321428613 : Rat) / 64000000000000000000), D0 := ((177197760547321428613 : Rat) / 64000000000000000000), D1 := ((60879354147321428613 : Rat) / 64000000000000000000), D2 := ((13489920547321428613 : Rat) / 64000000000000000000), D3 := ((15282922165178572281 : Rat) / 320000000000000000000), D4 := ((12816388058035633777 : Rat) / 800000000000000000000), LB := ((1902723848861143 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((177197760547321428613 : Rat) / 64000000000000000000), R := ((1107583970870535714551 : Rat) / 400000000000000000000), D0 := ((1107583970870535714551 : Rat) / 400000000000000000000), D1 := ((380593930870535714551 : Rat) / 400000000000000000000), D2 := ((84409970870535714551 : Rat) / 400000000000000000000), D3 := ((19201620156250001071 : Rat) / 400000000000000000000), D4 := ((1009636252678564987 : Rat) / 64000000000000000000), LB := ((34307402489611 : Rat) / 39062500000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1107583970870535714551 : Rat) / 400000000000000000000), R := ((4430727753281250001083 : Rat) / 1600000000000000000000), D0 := ((4430727753281250001083 : Rat) / 1600000000000000000000), D1 := ((1522767593281250001083 : Rat) / 1600000000000000000000), D2 := ((338031753281250001083 : Rat) / 1600000000000000000000), D3 := ((77198350424107147163 : Rat) / 1600000000000000000000), D4 := ((6212259129464245449 : Rat) / 400000000000000000000), LB := ((256013753299561 : Rat) / 250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4430727753281250001083 : Rat) / 1600000000000000000000), R := ((2215559811540178571981 : Rat) / 800000000000000000000), D0 := ((2215559811540178571981 : Rat) / 800000000000000000000), D1 := ((761579731540178571981 : Rat) / 800000000000000000000), D2 := ((169211811540178571981 : Rat) / 800000000000000000000), D3 := ((38795110111607145021 : Rat) / 800000000000000000000), D4 := ((24457166718749838917 : Rat) / 1600000000000000000000), LB := ((93684653690051 : Rat) / 78125000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2215559811540178571981 : Rat) / 800000000000000000000), R := ((110797584066964285743 : Rat) / 40000000000000000000), D0 := ((110797584066964285743 : Rat) / 40000000000000000000), D1 := ((38098580066964285743 : Rat) / 40000000000000000000), D2 := ((8480184066964285743 : Rat) / 40000000000000000000), D3 := ((391869799107142879 : Rat) / 8000000000000000000), D4 := ((12032648459821348019 : Rat) / 800000000000000000000), LB := ((1399884085040437 : Rat) / 5000000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110797584066964285743 : Rat) / 40000000000000000000), R := ((2216343551138392857739 : Rat) / 800000000000000000000), D0 := ((2216343551138392857739 : Rat) / 800000000000000000000), D1 := ((762363471138392857739 : Rat) / 800000000000000000000), D2 := ((169995551138392857739 : Rat) / 800000000000000000000), D3 := ((39578849709821430779 : Rat) / 800000000000000000000), D4 := ((582038933035710257 : Rat) / 40000000000000000000), LB := ((5127918196491943 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2216343551138392857739 : Rat) / 800000000000000000000), R := ((1108367710468750000309 : Rat) / 400000000000000000000), D0 := ((1108367710468750000309 : Rat) / 400000000000000000000), D1 := ((381377670468750000309 : Rat) / 400000000000000000000), D2 := ((85193710468750000309 : Rat) / 400000000000000000000), D3 := ((19985359754464286829 : Rat) / 400000000000000000000), D4 := ((11248908861607062261 : Rat) / 800000000000000000000), LB := ((2888848737335331 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1108367710468750000309 : Rat) / 400000000000000000000), R := ((2217127290736607143497 : Rat) / 800000000000000000000), D0 := ((2217127290736607143497 : Rat) / 800000000000000000000), D1 := ((763147210736607143497 : Rat) / 800000000000000000000), D2 := ((170779290736607143497 : Rat) / 800000000000000000000), D3 := ((40362589308035716537 : Rat) / 800000000000000000000), D4 := ((5428519531249959691 : Rat) / 400000000000000000000), LB := ((19361631155099257 : Rat) / 10000000000000000000) }
]

def block173RightChunk000L : Rat := ((44586488839285714323 : Rat) / 25000000000000000000)
def block173RightChunk000R : Rat := ((2217127290736607143497 : Rat) / 800000000000000000000)

def block173RightChunk000Certificate : Bool :=
  allBoxesValid block173RightChunk000 &&
  coversFromBool block173RightChunk000 block173RightChunk000L block173RightChunk000R

theorem block173RightChunk000Certificate_eq_true :
    block173RightChunk000Certificate = true := by
  native_decide

def block173RightChunk001 : List RatBox := [
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2217127290736607143497 : Rat) / 800000000000000000000), R := ((277189895066964285797 : Rat) / 100000000000000000000), D0 := ((277189895066964285797 : Rat) / 100000000000000000000), D1 := ((95442385066964285797 : Rat) / 100000000000000000000), D2 := ((21396395066964285797 : Rat) / 100000000000000000000), D3 := ((5094307388392857427 : Rat) / 100000000000000000000), D4 := ((10465169263392776503 : Rat) / 800000000000000000000), LB := ((14315851655509193 : Rat) / 5000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((277189895066964285797 : Rat) / 100000000000000000000), R := ((1109151450066964286067 : Rat) / 400000000000000000000), D0 := ((1109151450066964286067 : Rat) / 400000000000000000000), D1 := ((382161410066964286067 : Rat) / 400000000000000000000), D2 := ((85977450066964286067 : Rat) / 400000000000000000000), D3 := ((20769099352678572587 : Rat) / 400000000000000000000), D4 := ((1259162433035704203 : Rat) / 100000000000000000000), LB := ((1233448277017657 : Rat) / 1000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109151450066964286067 : Rat) / 400000000000000000000), R := ((554771659933035714473 : Rat) / 200000000000000000000), D0 := ((554771659933035714473 : Rat) / 200000000000000000000), D1 := ((191276639933035714473 : Rat) / 200000000000000000000), D2 := ((43184659933035714473 : Rat) / 200000000000000000000), D3 := ((10580484575892857733 : Rat) / 200000000000000000000), D4 := ((4644779933035673933 : Rat) / 400000000000000000000), LB := ((985406654095397 : Rat) / 250000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554771659933035714473 : Rat) / 200000000000000000000), R := ((69395441216517857169 : Rat) / 25000000000000000000), D0 := ((69395441216517857169 : Rat) / 25000000000000000000), D1 := ((23958563716517857169 : Rat) / 25000000000000000000), D2 := ((5447066216517857169 : Rat) / 25000000000000000000), D3 := ((2743088593750000153 : Rat) / 50000000000000000000), D4 := ((2126455066964265527 : Rat) / 200000000000000000000), LB := ((21576285279583107 : Rat) / 10000000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((69395441216517857169 : Rat) / 25000000000000000000), R := ((55594726933035714311 : Rat) / 20000000000000000000), D0 := ((55594726933035714311 : Rat) / 20000000000000000000), D1 := ((19245224933035714311 : Rat) / 20000000000000000000), D2 := ((4436026933035714311 : Rat) / 20000000000000000000), D3 := ((1175609397321428637 : Rat) / 20000000000000000000), D4 := ((216823158482140331 : Rat) / 25000000000000000000), LB := ((4855173290431447 : Rat) / 2500000000000000000) },
  { w1 := ((9061190969386619 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((8474575213639879 : Rat) / 50000000000000000), w4 := ((156114527914929 : Rat) / 1562500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55594726933035714311 : Rat) / 20000000000000000000), R := ((139182752232142857217 : Rat) / 50000000000000000000), D0 := ((139182752232142857217 : Rat) / 50000000000000000000), D1 := ((48308997232142857217 : Rat) / 50000000000000000000), D2 := ((11286002232142857217 : Rat) / 50000000000000000000), D3 := ((391869799107142879 : Rat) / 6250000000000000000), D4 := ((95084566964283689 : Rat) / 20000000000000000000), LB := ((4081093239354833 : Rat) / 100000000000000000) }
]

def block173RightChunk001L : Rat := ((2217127290736607143497 : Rat) / 800000000000000000000)
def block173RightChunk001R : Rat := ((139182752232142857217 : Rat) / 50000000000000000000)

def block173RightChunk001Certificate : Bool :=
  allBoxesValid block173RightChunk001 &&
  coversFromBool block173RightChunk001 block173RightChunk001L block173RightChunk001R

theorem block173RightChunk001Certificate_eq_true :
    block173RightChunk001Certificate = true := by
  native_decide

def block173RightChainCertificate : Bool :=
  decide (
    block173RightL = ((44586488839285714323 : Rat) / 25000000000000000000) /\
    ((2217127290736607143497 : Rat) / 800000000000000000000) = ((2217127290736607143497 : Rat) / 800000000000000000000) /\
    ((139182752232142857217 : Rat) / 50000000000000000000) = block173RightR)

theorem block173RightChainCertificate_eq_true :
    block173RightChainCertificate = true := by
  native_decide

def block173LeftBoxCount : Nat := boxCount block173LeftBoxes
def block173RightBoxCount : Nat := 106

def block173_rational_certificate : Prop :=
    block173LeftCertificate = true /\
    block173RightChainCertificate = true /\
    block173RightChunk000Certificate = true /\
    block173RightChunk001Certificate = true

theorem block173_rational_certificate_proof :
    block173_rational_certificate := by
  exact ⟨block173LeftCertificate_eq_true, block173RightChainCertificate_eq_true, block173RightChunk000Certificate_eq_true, block173RightChunk001Certificate_eq_true⟩

end Block173
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block173

open Set

def block173W1 : Rat := ((9061190969386619 : Rat) / 5000000000000000)
def block173W2 : Rat := (0 : Rat)
def block173W3 : Rat := ((8474575213639879 : Rat) / 50000000000000000)
def block173W4 : Rat := ((156114527914929 : Rat) / 1562500000000000)
def block173S1 : Rat := ((18174751 : Rat) / 10000000)
def block173S2 : Rat := ((511587 : Rat) / 200000)
def block173S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block173S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block173V (y : ℝ) : ℝ :=
  ratPotential block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4 y

def block173LeftParamsCertificate : Bool :=
  allBoxesSameParams block173LeftBoxes block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4

theorem block173LeftParamsCertificate_eq_true :
    block173LeftParamsCertificate = true := by
  native_decide

theorem block173_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173LeftL : ℝ) (block173LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  have hcert := block173LeftCertificate_eq_true
  unfold block173LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block173LeftBoxes) (lo := block173LeftL) (hi := block173LeftR)
    (w1 := block173W1) (w2 := block173W2) (w3 := block173W3) (w4 := block173W4)
    (s1 := block173S1) (s2 := block173S2) (s3 := block173S3) (s4 := block173S4)
    hboxes hcover block173LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block173RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block173RightChunk000 block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4

theorem block173RightChunk000ParamsCertificate_eq_true :
    block173RightChunk000ParamsCertificate = true := by
  native_decide

theorem block173_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173RightChunk000L : ℝ) (block173RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  have hcert := block173RightChunk000Certificate_eq_true
  unfold block173RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block173RightChunk000) (lo := block173RightChunk000L) (hi := block173RightChunk000R)
    (w1 := block173W1) (w2 := block173W2) (w3 := block173W3) (w4 := block173W4)
    (s1 := block173S1) (s2 := block173S2) (s3 := block173S3) (s4 := block173S4)
    hboxes hcover block173RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block173RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block173RightChunk001 block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4

theorem block173RightChunk001ParamsCertificate_eq_true :
    block173RightChunk001ParamsCertificate = true := by
  native_decide

theorem block173_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173RightChunk001L : ℝ) (block173RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  have hcert := block173RightChunk001Certificate_eq_true
  unfold block173RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block173RightChunk001) (lo := block173RightChunk001L) (hi := block173RightChunk001R)
    (w1 := block173W1) (w2 := block173W2) (w3 := block173W3) (w4 := block173W4)
    (s1 := block173S1) (s2 := block173S2) (s3 := block173S3) (s4 := block173S4)
    hboxes hcover block173RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block173_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173RightL : ℝ) (block173RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  by_cases h0 : y ≤ (block173RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block173RightChunk000L : ℝ) (block173RightChunk000R : ℝ) := by
      have hL : (block173RightChunk000L : ℝ) = (block173RightL : ℝ) := by
        norm_num [block173RightChunk000L, block173RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block173_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block173RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block173RightChunk001L : ℝ) = (block173RightChunk000R : ℝ) := by
      norm_num [block173RightChunk001L, block173RightChunk000R]
    have hR : (block173RightChunk001R : ℝ) = (block173RightR : ℝ) := by
      norm_num [block173RightChunk001R, block173RightR]
    have hyc : y ∈ Icc (block173RightChunk001L : ℝ) (block173RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block173_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block173_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block173LeftL : ℝ) (block173LeftR : ℝ) →
    y ≠ 0 → y ≠ (block173S1 : ℝ) → y ≠ (block173S2 : ℝ) →
    y ≠ (block173S3 : ℝ) → y ≠ (block173S4 : ℝ) → 0 < block173V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block173RightL : ℝ) (block173RightR : ℝ) →
    y ≠ 0 → y ≠ (block173S1 : ℝ) → y ≠ (block173S2 : ℝ) →
    y ≠ (block173S3 : ℝ) → y ≠ (block173S4 : ℝ) → 0 < block173V y)

theorem block173_reallog_certificate_proof :
    block173_reallog_certificate := by
  exact ⟨block173_left_V_pos, block173_right_V_pos⟩

end Block173
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block173.block173V
#check Erdos1038Lean.M1817475.Block173.block173_left_V_pos
#check Erdos1038Lean.M1817475.Block173.block173_right_V_pos
#check Erdos1038Lean.M1817475.Block173.block173_reallog_certificate_proof
