/-
Self-contained Lean4Web paste file.
Block 174 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block174

def block174LeftL : Rat := ((1566528125000000003 : Rat) / 2000000000000000000)
def block174LeftR : Rat := ((19586488839285714323 : Rat) / 25000000000000000000)
def block174RightL : Rat := ((3566528125000000003 : Rat) / 2000000000000000000)
def block174RightR : Rat := ((69586488839285714323 : Rat) / 25000000000000000000)

def block174LeftBoxes : List RatBox := [
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1566528125000000003 : Rat) / 2000000000000000000), R := ((19586488839285714323 : Rat) / 25000000000000000000), D0 := ((19586488839285714323 : Rat) / 25000000000000000000), D1 := ((2068422074999999997 : Rat) / 2000000000000000000), D2 := ((3549341874999999997 : Rat) / 2000000000000000000), D3 := ((9688459071428571411 : Rat) / 5000000000000000000), D4 := ((4002453024999999797 : Rat) / 2000000000000000000), LB := ((16639258653744077 : Rat) / 10000000000000000000) }
]

def block174LeftCertificate : Bool :=
  allBoxesValid block174LeftBoxes &&
  coversFromBool block174LeftBoxes block174LeftL block174LeftR

theorem block174LeftCertificate_eq_true :
    block174LeftCertificate = true := by
  native_decide

def block174RightChunk000 : List RatBox := [
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3566528125000000003 : Rat) / 2000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((68422074999999997 : Rat) / 2000000000000000000), D2 := ((1549341874999999997 : Rat) / 2000000000000000000), D3 := ((4688459071428571411 : Rat) / 5000000000000000000), D4 := ((2002453024999999797 : Rat) / 2000000000000000000), LB := ((2758941225234523 : Rat) / 500000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((1034860905708853 : Rat) / 1000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((35799485549542853 : Rat) / 100000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((939962192393853 : Rat) / 6250000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((4245888233323223 : Rat) / 50000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((825080934328791 : Rat) / 12500000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((1412065842627519 : Rat) / 50000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((34553020374354093 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((3769935294764673 : Rat) / 500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((2827352806532013 : Rat) / 250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((13610302913333927 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((27248766404601443 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((2951086119474311 : Rat) / 500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((4245279397668639 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((339053296740853 : Rat) / 125000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((6539743566165851 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((456028645873241 : Rat) / 12500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((22652988813422203 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((3494281009609801 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((1581896155727 : Rat) / 1250000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((1642310866432739 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((10370260426063871 : Rat) / 25000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((59080885326801 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((3469901212961521 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((12379283328776969 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((439248030629269 : Rat) / 400000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((4843232028177019 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((1062025228824523 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((926445628262329 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((6433727478840079 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((2781943266789433 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((1200815918807191 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((1038276295424051 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((36146827994099073 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((31892944421541003 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((14391324572533837 : Rat) / 50000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((6707366651793889 : Rat) / 25000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((26047205401660833 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((2644996630611629 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((7013037651000531 : Rat) / 25000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((15434234354343157 : Rat) / 50000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((436424363789191 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((5025493451244617 : Rat) / 12500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((46754157004638697 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((545806169903823 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((3184986227410397 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((7412824468117363 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((4294166078557121 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((2474562254142637 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((11344368821785689 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((1616065859966001 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((1465260132981011 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((8259257248295071 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((21889895376081547 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((6670544530199829 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((5876039972822489 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((1745113813049537 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((23786147480839293 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((96176511631481 : Rat) / 31250000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((19221268321366891 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((1809239627260581 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((4183998777739853 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((13886728249668731 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((105694170237541 : Rat) / 62500000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((3945557186973883 : Rat) / 500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((1960839003470171 : Rat) / 625000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((1415054679894459 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((1826167301774001 : Rat) / 20000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((547316359196428571201 : Rat) / 200000000000000000000), D0 := ((547316359196428571201 : Rat) / 200000000000000000000), D1 := ((183821339196428571201 : Rat) / 200000000000000000000), D2 := ((35729359196428571201 : Rat) / 200000000000000000000), D3 := ((3125183839285714461 : Rat) / 200000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((12740202747429907 : Rat) / 100000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((547316359196428571201 : Rat) / 200000000000000000000), R := ((275220771517857142831 : Rat) / 100000000000000000000), D0 := ((275220771517857142831 : Rat) / 100000000000000000000), D1 := ((93473261517857142831 : Rat) / 100000000000000000000), D2 := ((19427271517857142831 : Rat) / 100000000000000000000), D3 := ((3125183839285714461 : Rat) / 100000000000000000000), D4 := ((9581755803571408799 : Rat) / 200000000000000000000), LB := ((3539112032528019 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275220771517857142831 : Rat) / 100000000000000000000), R := ((2204891355982142857109 : Rat) / 800000000000000000000), D0 := ((2204891355982142857109 : Rat) / 800000000000000000000), D1 := ((750911275982142857109 : Rat) / 800000000000000000000), D2 := ((158543355982142857109 : Rat) / 800000000000000000000), D3 := ((28126654553571430149 : Rat) / 800000000000000000000), D4 := ((3228285982142847169 : Rat) / 100000000000000000000), LB := ((11698430250046021 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2204891355982142857109 : Rat) / 800000000000000000000), R := ((4412907895803571428679 : Rat) / 1600000000000000000000), D0 := ((4412907895803571428679 : Rat) / 1600000000000000000000), D1 := ((1504947735803571428679 : Rat) / 1600000000000000000000), D2 := ((320211895803571428679 : Rat) / 1600000000000000000000), D3 := ((59378492946428574759 : Rat) / 1600000000000000000000), D4 := ((22701104017857062891 : Rat) / 800000000000000000000), LB := ((10867270687872799 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4412907895803571428679 : Rat) / 1600000000000000000000), R := ((220801653982142857157 : Rat) / 80000000000000000000), D0 := ((220801653982142857157 : Rat) / 80000000000000000000), D1 := ((75403645982142857157 : Rat) / 80000000000000000000), D2 := ((16166853982142857157 : Rat) / 80000000000000000000), D3 := ((3125183839285714461 : Rat) / 80000000000000000000), D4 := ((42277024196428411321 : Rat) / 1600000000000000000000), LB := ((4779132877192449 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220801653982142857157 : Rat) / 80000000000000000000), R := ((8835191343125000000741 : Rat) / 3200000000000000000000), D0 := ((8835191343125000000741 : Rat) / 3200000000000000000000), D1 := ((3019271023125000000741 : Rat) / 3200000000000000000000), D2 := ((649799343125000000741 : Rat) / 3200000000000000000000), D3 := ((128132537410714292901 : Rat) / 3200000000000000000000), D4 := ((1957592017857134843 : Rat) / 80000000000000000000), LB := ((2996700092900789 : Rat) / 500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8835191343125000000741 : Rat) / 3200000000000000000000), R := ((4419158263482142857601 : Rat) / 1600000000000000000000), D0 := ((4419158263482142857601 : Rat) / 1600000000000000000000), D1 := ((1511198103482142857601 : Rat) / 1600000000000000000000), D2 := ((326462263482142857601 : Rat) / 1600000000000000000000), D3 := ((65628860625000003681 : Rat) / 1600000000000000000000), D4 := ((75178496874999679259 : Rat) / 3200000000000000000000), LB := ((18612427585461 : Rat) / 5000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4419158263482142857601 : Rat) / 1600000000000000000000), R := ((8841441710803571429663 : Rat) / 3200000000000000000000), D0 := ((8841441710803571429663 : Rat) / 3200000000000000000000), D1 := ((3025521390803571429663 : Rat) / 3200000000000000000000), D2 := ((656049710803571429663 : Rat) / 3200000000000000000000), D3 := ((134382905089285721823 : Rat) / 3200000000000000000000), D4 := ((36026656517856982399 : Rat) / 1600000000000000000000), LB := ((3444307670486313 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8841441710803571429663 : Rat) / 3200000000000000000000), R := ((2211141723660714286031 : Rat) / 800000000000000000000), D0 := ((2211141723660714286031 : Rat) / 800000000000000000000), D1 := ((757161643660714286031 : Rat) / 800000000000000000000), D2 := ((164793723660714286031 : Rat) / 800000000000000000000), D3 := ((34377022232142859071 : Rat) / 800000000000000000000), D4 := ((68928129196428250337 : Rat) / 3200000000000000000000), LB := ((323011911834703 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2211141723660714286031 : Rat) / 800000000000000000000), R := ((17692258973125000002709 : Rat) / 6400000000000000000000), D0 := ((17692258973125000002709 : Rat) / 6400000000000000000000), D1 := ((6060418333125000002709 : Rat) / 6400000000000000000000), D2 := ((1321474973125000002709 : Rat) / 6400000000000000000000), D3 := ((278141361696428587029 : Rat) / 6400000000000000000000), D4 := ((16450736339285633969 : Rat) / 800000000000000000000), LB := ((7941734880343443 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17692258973125000002709 : Rat) / 6400000000000000000000), R := ((1769538415696428571717 : Rat) / 640000000000000000000), D0 := ((1769538415696428571717 : Rat) / 640000000000000000000), D1 := ((606354351696428571717 : Rat) / 640000000000000000000), D2 := ((132460015696428571717 : Rat) / 640000000000000000000), D3 := ((28126654553571430149 : Rat) / 640000000000000000000), D4 := ((128480706874999357291 : Rat) / 6400000000000000000000), LB := ((9700950017045851 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1769538415696428571717 : Rat) / 640000000000000000000), R := ((17698509340803571431631 : Rat) / 6400000000000000000000), D0 := ((17698509340803571431631 : Rat) / 6400000000000000000000), D1 := ((6066668700803571431631 : Rat) / 6400000000000000000000), D2 := ((1327725340803571431631 : Rat) / 6400000000000000000000), D3 := ((284391729375000015951 : Rat) / 6400000000000000000000), D4 := ((12535552303571364283 : Rat) / 640000000000000000000), LB := ((4322332892559011 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17698509340803571431631 : Rat) / 6400000000000000000000), R := ((35400143865446428577723 : Rat) / 12800000000000000000000), D0 := ((35400143865446428577723 : Rat) / 12800000000000000000000), D1 := ((12136462585446428577723 : Rat) / 12800000000000000000000), D2 := ((2658575865446428577723 : Rat) / 12800000000000000000000), D3 := ((571908642589285746363 : Rat) / 12800000000000000000000), D4 := ((122230339196427928369 : Rat) / 6400000000000000000000), LB := ((2916165038485019 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35400143865446428577723 : Rat) / 12800000000000000000000), R := ((4425408631160714286523 : Rat) / 1600000000000000000000), D0 := ((4425408631160714286523 : Rat) / 1600000000000000000000), D1 := ((1517448471160714286523 : Rat) / 1600000000000000000000), D2 := ((332712631160714286523 : Rat) / 1600000000000000000000), D3 := ((71879228303571432603 : Rat) / 1600000000000000000000), D4 := ((241335494553570142277 : Rat) / 12800000000000000000000), LB := ((12573916981595823 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4425408631160714286523 : Rat) / 1600000000000000000000), R := ((7081278846625000001329 : Rat) / 2560000000000000000000), D0 := ((7081278846625000001329 : Rat) / 2560000000000000000000), D1 := ((2428542590625000001329 : Rat) / 2560000000000000000000), D2 := ((532965246625000001329 : Rat) / 2560000000000000000000), D3 := ((115631802053571435057 : Rat) / 2560000000000000000000), D4 := ((29776288839285553477 : Rat) / 1600000000000000000000), LB := ((2696338266468673 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7081278846625000001329 : Rat) / 2560000000000000000000), R := ((17704759708482142860553 : Rat) / 6400000000000000000000), D0 := ((17704759708482142860553 : Rat) / 6400000000000000000000), D1 := ((6072919068482142860553 : Rat) / 6400000000000000000000), D2 := ((1333975708482142860553 : Rat) / 6400000000000000000000), D3 := ((290642097053571444873 : Rat) / 6400000000000000000000), D4 := ((47017025374999742671 : Rat) / 2560000000000000000000), LB := ((9218994013726611 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17704759708482142860553 : Rat) / 6400000000000000000000), R := ((35412644600803571435567 : Rat) / 12800000000000000000000), D0 := ((35412644600803571435567 : Rat) / 12800000000000000000000), D1 := ((12148963320803571435567 : Rat) / 12800000000000000000000), D2 := ((2671076600803571435567 : Rat) / 12800000000000000000000), D3 := ((584409377946428604207 : Rat) / 12800000000000000000000), D4 := ((115979971517856499447 : Rat) / 6400000000000000000000), LB := ((7878885289939741 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35412644600803571435567 : Rat) / 12800000000000000000000), R := ((8853942446160714287507 : Rat) / 3200000000000000000000), D0 := ((8853942446160714287507 : Rat) / 3200000000000000000000), D1 := ((3038022126160714287507 : Rat) / 3200000000000000000000), D2 := ((668550446160714287507 : Rat) / 3200000000000000000000), D3 := ((146883640446428579667 : Rat) / 3200000000000000000000), D4 := ((228834759196427284433 : Rat) / 12800000000000000000000), LB := ((1353853306910291 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8853942446160714287507 : Rat) / 3200000000000000000000), R := ((35418894968482142864489 : Rat) / 12800000000000000000000), D0 := ((35418894968482142864489 : Rat) / 12800000000000000000000), D1 := ((12155213688482142864489 : Rat) / 12800000000000000000000), D2 := ((2677326968482142864489 : Rat) / 12800000000000000000000), D3 := ((590659745625000033129 : Rat) / 12800000000000000000000), D4 := ((56427393839285392493 : Rat) / 3200000000000000000000), LB := ((5894581482516759 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35418894968482142864489 : Rat) / 12800000000000000000000), R := ((708440403046428571579 : Rat) / 256000000000000000000), D0 := ((708440403046428571579 : Rat) / 256000000000000000000), D1 := ((243166777446428571579 : Rat) / 256000000000000000000), D2 := ((53609043046428571579 : Rat) / 256000000000000000000), D3 := ((59378492946428574759 : Rat) / 1280000000000000000000), D4 := ((222584391517855855511 : Rat) / 12800000000000000000000), LB := ((210379542972583 : Rat) / 400000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((708440403046428571579 : Rat) / 256000000000000000000), R := ((35425145336160714293411 : Rat) / 12800000000000000000000), D0 := ((35425145336160714293411 : Rat) / 12800000000000000000000), D1 := ((12161464056160714293411 : Rat) / 12800000000000000000000), D2 := ((2683577336160714293411 : Rat) / 12800000000000000000000), D3 := ((596910113303571462051 : Rat) / 12800000000000000000000), D4 := ((4389184153571402821 : Rat) / 256000000000000000000), LB := ((48688723131085077 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35425145336160714293411 : Rat) / 12800000000000000000000), R := ((553566726875000000123 : Rat) / 200000000000000000000), D0 := ((553566726875000000123 : Rat) / 200000000000000000000), D1 := ((190071706875000000123 : Rat) / 200000000000000000000), D2 := ((41979726875000000123 : Rat) / 200000000000000000000), D3 := ((9375551517857143383 : Rat) / 200000000000000000000), D4 := ((216334023839284426589 : Rat) / 12800000000000000000000), LB := ((47278554284496677 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553566726875000000123 : Rat) / 200000000000000000000), R := ((35431395703839285722333 : Rat) / 12800000000000000000000), D0 := ((35431395703839285722333 : Rat) / 12800000000000000000000), D1 := ((12167714423839285722333 : Rat) / 12800000000000000000000), D2 := ((2689827703839285722333 : Rat) / 12800000000000000000000), D3 := ((603160480982142890973 : Rat) / 12800000000000000000000), D4 := ((3331388124999979877 : Rat) / 200000000000000000000), LB := ((4841811912689731 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35431395703839285722333 : Rat) / 12800000000000000000000), R := ((17717260443839285718397 : Rat) / 6400000000000000000000), D0 := ((17717260443839285718397 : Rat) / 6400000000000000000000), D1 := ((6085419803839285718397 : Rat) / 6400000000000000000000), D2 := ((1346476443839285718397 : Rat) / 6400000000000000000000), D3 := ((303142832410714302717 : Rat) / 6400000000000000000000), D4 := ((210083656160712997667 : Rat) / 12800000000000000000000), LB := ((5216381002373649 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17717260443839285718397 : Rat) / 6400000000000000000000), R := ((7087529214303571430251 : Rat) / 2560000000000000000000), D0 := ((7087529214303571430251 : Rat) / 2560000000000000000000), D1 := ((2434792958303571430251 : Rat) / 2560000000000000000000), D2 := ((539215614303571430251 : Rat) / 2560000000000000000000), D3 := ((121882169732142863979 : Rat) / 2560000000000000000000), D4 := ((103479236160713641603 : Rat) / 6400000000000000000000), LB := ((1464370545834759 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7087529214303571430251 : Rat) / 2560000000000000000000), R := ((8860192813839285716429 : Rat) / 3200000000000000000000), D0 := ((8860192813839285716429 : Rat) / 3200000000000000000000), D1 := ((3044272493839285716429 : Rat) / 3200000000000000000000), D2 := ((674800813839285716429 : Rat) / 3200000000000000000000), D3 := ((153134008125000008589 : Rat) / 3200000000000000000000), D4 := ((40766657696428313749 : Rat) / 2560000000000000000000), LB := ((6771331306296147 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8860192813839285716429 : Rat) / 3200000000000000000000), R := ((35443896439196428580177 : Rat) / 12800000000000000000000), D0 := ((35443896439196428580177 : Rat) / 12800000000000000000000), D1 := ((12180215159196428580177 : Rat) / 12800000000000000000000), D2 := ((2702328439196428580177 : Rat) / 12800000000000000000000), D3 := ((615661216339285748817 : Rat) / 12800000000000000000000), D4 := ((50177026160713963571 : Rat) / 3200000000000000000000), LB := ((1991114477013639 : Rat) / 2500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35443896439196428580177 : Rat) / 12800000000000000000000), R := ((17723510811517857147319 : Rat) / 6400000000000000000000), D0 := ((17723510811517857147319 : Rat) / 6400000000000000000000), D1 := ((6091670171517857147319 : Rat) / 6400000000000000000000), D2 := ((1352726811517857147319 : Rat) / 6400000000000000000000), D3 := ((309393200089285731639 : Rat) / 6400000000000000000000), D4 := ((197582920803570139823 : Rat) / 12800000000000000000000), LB := ((1888744768422157 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17723510811517857147319 : Rat) / 6400000000000000000000), R := ((35450146806875000009099 : Rat) / 12800000000000000000000), D0 := ((35450146806875000009099 : Rat) / 12800000000000000000000), D1 := ((12186465526875000009099 : Rat) / 12800000000000000000000), D2 := ((2708578806875000009099 : Rat) / 12800000000000000000000), D3 := ((621911584017857177739 : Rat) / 12800000000000000000000), D4 := ((97228868482142212681 : Rat) / 6400000000000000000000), LB := ((11216343333501633 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35450146806875000009099 : Rat) / 12800000000000000000000), R := ((886331799767857143089 : Rat) / 320000000000000000000), D0 := ((886331799767857143089 : Rat) / 320000000000000000000), D1 := ((304739767767857143089 : Rat) / 320000000000000000000), D2 := ((67792599767857143089 : Rat) / 320000000000000000000), D3 := ((3125183839285714461 : Rat) / 64000000000000000000), D4 := ((191332553124998710901 : Rat) / 12800000000000000000000), LB := ((1328990458335011 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((886331799767857143089 : Rat) / 320000000000000000000), R := ((17729761179196428576241 : Rat) / 6400000000000000000000), D0 := ((17729761179196428576241 : Rat) / 6400000000000000000000), D1 := ((6097920539196428576241 : Rat) / 6400000000000000000000), D2 := ((1358977179196428576241 : Rat) / 6400000000000000000000), D3 := ((315643567767857160561 : Rat) / 6400000000000000000000), D4 := ((4705184232142824911 : Rat) / 320000000000000000000), LB := ((857580321349527 : Rat) / 5000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17729761179196428576241 : Rat) / 6400000000000000000000), R := ((8866443181517857145351 : Rat) / 3200000000000000000000), D0 := ((8866443181517857145351 : Rat) / 3200000000000000000000), D1 := ((3050522861517857145351 : Rat) / 3200000000000000000000), D2 := ((681051181517857145351 : Rat) / 3200000000000000000000), D3 := ((159384375803571437511 : Rat) / 3200000000000000000000), D4 := ((90978500803570783759 : Rat) / 6400000000000000000000), LB := ((1505297063083999 : Rat) / 2000000000000000000) }
]

def block174RightChunk000L : Rat := ((3566528125000000003 : Rat) / 2000000000000000000)
def block174RightChunk000R : Rat := ((8866443181517857145351 : Rat) / 3200000000000000000000)

def block174RightChunk000Certificate : Bool :=
  allBoxesValid block174RightChunk000 &&
  coversFromBool block174RightChunk000 block174RightChunk000L block174RightChunk000R

theorem block174RightChunk000Certificate_eq_true :
    block174RightChunk000Certificate = true := by
  native_decide

def block174RightChunk001 : List RatBox := [
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8866443181517857145351 : Rat) / 3200000000000000000000), R := ((17736011546875000005163 : Rat) / 6400000000000000000000), D0 := ((17736011546875000005163 : Rat) / 6400000000000000000000), D1 := ((6104170906875000005163 : Rat) / 6400000000000000000000), D2 := ((1365227546875000005163 : Rat) / 6400000000000000000000), D3 := ((321893935446428589483 : Rat) / 6400000000000000000000), D4 := ((43926658482142534649 : Rat) / 3200000000000000000000), LB := ((14678818640246893 : Rat) / 10000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17736011546875000005163 : Rat) / 6400000000000000000000), R := ((2217392091339285714953 : Rat) / 800000000000000000000), D0 := ((2217392091339285714953 : Rat) / 800000000000000000000), D1 := ((763412011339285714953 : Rat) / 800000000000000000000), D2 := ((171044091339285714953 : Rat) / 800000000000000000000), D3 := ((40627389910714287993 : Rat) / 800000000000000000000), D4 := ((84728133124999354837 : Rat) / 6400000000000000000000), LB := ((2325323394608947 : Rat) / 1000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2217392091339285714953 : Rat) / 800000000000000000000), R := ((8872693549196428574273 : Rat) / 3200000000000000000000), D0 := ((8872693549196428574273 : Rat) / 3200000000000000000000), D1 := ((3056773229196428574273 : Rat) / 3200000000000000000000), D2 := ((687301549196428574273 : Rat) / 3200000000000000000000), D3 := ((165634743482142866433 : Rat) / 3200000000000000000000), D4 := ((10200368660714205047 : Rat) / 800000000000000000000), LB := ((310481922150857 : Rat) / 500000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8872693549196428574273 : Rat) / 3200000000000000000000), R := ((4437909366517857144367 : Rat) / 1600000000000000000000), D0 := ((4437909366517857144367 : Rat) / 1600000000000000000000), D1 := ((1529949206517857144367 : Rat) / 1600000000000000000000), D2 := ((345213366517857144367 : Rat) / 1600000000000000000000), D3 := ((84379963660714290447 : Rat) / 1600000000000000000000), D4 := ((37676290803571105727 : Rat) / 3200000000000000000000), LB := ((3955954631712083 : Rat) / 1250000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4437909366517857144367 : Rat) / 1600000000000000000000), R := ((1110258637589285714707 : Rat) / 400000000000000000000), D0 := ((1110258637589285714707 : Rat) / 400000000000000000000), D1 := ((383268597589285714707 : Rat) / 400000000000000000000), D2 := ((87084637589285714707 : Rat) / 400000000000000000000), D3 := ((21876286875000001227 : Rat) / 400000000000000000000), D4 := ((17275553482142695633 : Rat) / 1600000000000000000000), LB := ((2380114136580569 : Rat) / 2000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1110258637589285714707 : Rat) / 400000000000000000000), R := ((17789139672142857151 : Rat) / 6400000000000000000), D0 := ((17789139672142857151 : Rat) / 6400000000000000000), D1 := ((6157299032142857151 : Rat) / 6400000000000000000), D2 := ((1418355672142857151 : Rat) / 6400000000000000000), D3 := ((9375551517857143383 : Rat) / 160000000000000000000), D4 := ((3537592410714245293 : Rat) / 400000000000000000000), LB := ((48570523613622463 : Rat) / 100000000000000000000) },
  { w1 := ((18086330405470201 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((8503927101404639 : Rat) / 50000000000000000), w4 := ((9949409340815091 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17789139672142857151 : Rat) / 6400000000000000000), R := ((69586488839285714323 : Rat) / 25000000000000000000), D0 := ((69586488839285714323 : Rat) / 25000000000000000000), D1 := ((24149611339285714323 : Rat) / 25000000000000000000), D2 := ((5638113839285714323 : Rat) / 25000000000000000000), D3 := ((3125183839285714461 : Rat) / 50000000000000000000), D4 := ((31600007857142209 : Rat) / 6400000000000000000), LB := ((4685838017055903 : Rat) / 125000000000000000) }
]

def block174RightChunk001L : Rat := ((8866443181517857145351 : Rat) / 3200000000000000000000)
def block174RightChunk001R : Rat := ((69586488839285714323 : Rat) / 25000000000000000000)

def block174RightChunk001Certificate : Bool :=
  allBoxesValid block174RightChunk001 &&
  coversFromBool block174RightChunk001 block174RightChunk001L block174RightChunk001R

theorem block174RightChunk001Certificate_eq_true :
    block174RightChunk001Certificate = true := by
  native_decide

def block174RightChainCertificate : Bool :=
  decide (
    block174RightL = ((3566528125000000003 : Rat) / 2000000000000000000) /\
    ((8866443181517857145351 : Rat) / 3200000000000000000000) = ((8866443181517857145351 : Rat) / 3200000000000000000000) /\
    ((69586488839285714323 : Rat) / 25000000000000000000) = block174RightR)

theorem block174RightChainCertificate_eq_true :
    block174RightChainCertificate = true := by
  native_decide

def block174LeftBoxCount : Nat := boxCount block174LeftBoxes
def block174RightBoxCount : Nat := 107

def block174_rational_certificate : Prop :=
    block174LeftCertificate = true /\
    block174RightChainCertificate = true /\
    block174RightChunk000Certificate = true /\
    block174RightChunk001Certificate = true

theorem block174_rational_certificate_proof :
    block174_rational_certificate := by
  exact ⟨block174LeftCertificate_eq_true, block174RightChainCertificate_eq_true, block174RightChunk000Certificate_eq_true, block174RightChunk001Certificate_eq_true⟩

end Block174
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block174

open Set

def block174W1 : Rat := ((18086330405470201 : Rat) / 10000000000000000)
def block174W2 : Rat := (0 : Rat)
def block174W3 : Rat := ((8503927101404639 : Rat) / 50000000000000000)
def block174W4 : Rat := ((9949409340815091 : Rat) / 100000000000000000)
def block174S1 : Rat := ((18174751 : Rat) / 10000000)
def block174S2 : Rat := ((511587 : Rat) / 200000)
def block174S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block174S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block174V (y : ℝ) : ℝ :=
  ratPotential block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4 y

def block174LeftParamsCertificate : Bool :=
  allBoxesSameParams block174LeftBoxes block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4

theorem block174LeftParamsCertificate_eq_true :
    block174LeftParamsCertificate = true := by
  native_decide

theorem block174_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174LeftL : ℝ) (block174LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  have hcert := block174LeftCertificate_eq_true
  unfold block174LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block174LeftBoxes) (lo := block174LeftL) (hi := block174LeftR)
    (w1 := block174W1) (w2 := block174W2) (w3 := block174W3) (w4 := block174W4)
    (s1 := block174S1) (s2 := block174S2) (s3 := block174S3) (s4 := block174S4)
    hboxes hcover block174LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block174RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block174RightChunk000 block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4

theorem block174RightChunk000ParamsCertificate_eq_true :
    block174RightChunk000ParamsCertificate = true := by
  native_decide

theorem block174_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174RightChunk000L : ℝ) (block174RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  have hcert := block174RightChunk000Certificate_eq_true
  unfold block174RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block174RightChunk000) (lo := block174RightChunk000L) (hi := block174RightChunk000R)
    (w1 := block174W1) (w2 := block174W2) (w3 := block174W3) (w4 := block174W4)
    (s1 := block174S1) (s2 := block174S2) (s3 := block174S3) (s4 := block174S4)
    hboxes hcover block174RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block174RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block174RightChunk001 block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4

theorem block174RightChunk001ParamsCertificate_eq_true :
    block174RightChunk001ParamsCertificate = true := by
  native_decide

theorem block174_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174RightChunk001L : ℝ) (block174RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  have hcert := block174RightChunk001Certificate_eq_true
  unfold block174RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block174RightChunk001) (lo := block174RightChunk001L) (hi := block174RightChunk001R)
    (w1 := block174W1) (w2 := block174W2) (w3 := block174W3) (w4 := block174W4)
    (s1 := block174S1) (s2 := block174S2) (s3 := block174S3) (s4 := block174S4)
    hboxes hcover block174RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block174_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174RightL : ℝ) (block174RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  by_cases h0 : y ≤ (block174RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block174RightChunk000L : ℝ) (block174RightChunk000R : ℝ) := by
      have hL : (block174RightChunk000L : ℝ) = (block174RightL : ℝ) := by
        norm_num [block174RightChunk000L, block174RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block174_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block174RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block174RightChunk001L : ℝ) = (block174RightChunk000R : ℝ) := by
      norm_num [block174RightChunk001L, block174RightChunk000R]
    have hR : (block174RightChunk001R : ℝ) = (block174RightR : ℝ) := by
      norm_num [block174RightChunk001R, block174RightR]
    have hyc : y ∈ Icc (block174RightChunk001L : ℝ) (block174RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block174_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block174_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block174LeftL : ℝ) (block174LeftR : ℝ) →
    y ≠ 0 → y ≠ (block174S1 : ℝ) → y ≠ (block174S2 : ℝ) →
    y ≠ (block174S3 : ℝ) → y ≠ (block174S4 : ℝ) → 0 < block174V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block174RightL : ℝ) (block174RightR : ℝ) →
    y ≠ 0 → y ≠ (block174S1 : ℝ) → y ≠ (block174S2 : ℝ) →
    y ≠ (block174S3 : ℝ) → y ≠ (block174S4 : ℝ) → 0 < block174V y)

theorem block174_reallog_certificate_proof :
    block174_reallog_certificate := by
  exact ⟨block174_left_V_pos, block174_right_V_pos⟩

end Block174
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block174.block174V
#check Erdos1038Lean.M1817475.Block174.block174_left_V_pos
#check Erdos1038Lean.M1817475.Block174.block174_right_V_pos
#check Erdos1038Lean.M1817475.Block174.block174_reallog_certificate_proof
