/-
Self-contained Lean4Web paste file.
Block 189 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block189

def block189LeftL : Rat := ((3901658482142857151 : Rat) / 5000000000000000000)
def block189LeftR : Rat := ((39026359375000000081 : Rat) / 50000000000000000000)
def block189RightL : Rat := ((8901658482142857151 : Rat) / 5000000000000000000)
def block189RightR : Rat := ((139026359375000000081 : Rat) / 50000000000000000000)

def block189LeftBoxes : List RatBox := [
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3901658482142857151 : Rat) / 5000000000000000000), R := ((39026359375000000081 : Rat) / 50000000000000000000), D0 := ((39026359375000000081 : Rat) / 50000000000000000000), D1 := ((5185717017857142849 : Rat) / 5000000000000000000), D2 := ((8888016517857142849 : Rat) / 5000000000000000000), D3 := ((3881248360714285707 : Rat) / 2000000000000000000), D4 := ((10020794392857142349 : Rat) / 5000000000000000000), LB := ((3763896608668417 : Rat) / 12500000000000000000) }
]

def block189LeftCertificate : Bool :=
  allBoxesValid block189LeftBoxes &&
  coversFromBool block189LeftBoxes block189LeftL block189LeftR

theorem block189LeftCertificate_eq_true :
    block189LeftCertificate = true := by
  native_decide

def block189RightChunk000 : List RatBox := [
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8901658482142857151 : Rat) / 5000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((185717017857142849 : Rat) / 5000000000000000000), D2 := ((3888016517857142849 : Rat) / 5000000000000000000), D3 := ((1881248360714285707 : Rat) / 2000000000000000000), D4 := ((5020794392857142349 : Rat) / 5000000000000000000), LB := ((1038706740005541 : Rat) / 200000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((2456591841197457 : Rat) / 2500000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((2056356032737891 : Rat) / 6250000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((2621623308831621 : Rat) / 20000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((7042464424973631 : Rat) / 100000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((10809866716788799 : Rat) / 200000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((4614607912327033 : Rat) / 250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((410899808767857142837 : Rat) / 160000000000000000000), D0 := ((410899808767857142837 : Rat) / 160000000000000000000), D1 := ((120103792767857142837 : Rat) / 160000000000000000000), D2 := ((1630208767857142837 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((11655642126953969 : Rat) / 500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((410899808767857142837 : Rat) / 160000000000000000000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 32000000000000000000), D4 := ((34618683232142841163 : Rat) / 160000000000000000000), LB := ((1152431604642859 : Rat) / 100000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((10717967886684499 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((829950661374999999859 : Rat) / 320000000000000000000), D0 := ((829950661374999999859 : Rat) / 320000000000000000000), D1 := ((248358629374999999859 : Rat) / 320000000000000000000), D2 := ((11411461374999999859 : Rat) / 320000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((1382850040062153 : Rat) / 250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((829950661374999999859 : Rat) / 320000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 12800000000000000000), D4 := ((61086322624999968141 : Rat) / 320000000000000000000), LB := ((7790816192739247 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((1664791949053571428229 : Rat) / 640000000000000000000), D0 := ((1664791949053571428229 : Rat) / 640000000000000000000), D1 := ((501607885053571428229 : Rat) / 640000000000000000000), D2 := ((27713549053571428229 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((9381579533412121 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1664791949053571428229 : Rat) / 640000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((76619812089285713339 : Rat) / 640000000000000000000), D4 := ((117282018946428507771 : Rat) / 640000000000000000000), LB := ((6141274297619681 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((1568896543607673 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((947601997125791 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((3340995359482142856317 : Rat) / 1280000000000000000000), D0 := ((3340995359482142856317 : Rat) / 1280000000000000000000), D1 := ((1014627231482142856317 : Rat) / 1280000000000000000000), D2 := ((66838559482142856317 : Rat) / 1280000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((2803334159533627 : Rat) / 1250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3340995359482142856317 : Rat) / 1280000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((141828162803571426819 : Rat) / 1280000000000000000000), D4 := ((223152576517857015683 : Rat) / 1280000000000000000000), LB := ((1037735824818177 : Rat) / 625000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((3344255777017857141991 : Rat) / 1280000000000000000000), D0 := ((3344255777017857141991 : Rat) / 1280000000000000000000), D1 := ((1017887649017857141991 : Rat) / 1280000000000000000000), D2 := ((70098977017857141991 : Rat) / 1280000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((444583734164683 : Rat) / 400000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3344255777017857141991 : Rat) / 1280000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((27713549053571428229 : Rat) / 256000000000000000000), D4 := ((219892158982142730009 : Rat) / 1280000000000000000000), LB := ((5965252084463579 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((669503238910714285533 : Rat) / 256000000000000000000), D0 := ((669503238910714285533 : Rat) / 256000000000000000000), D1 := ((204229613310714285533 : Rat) / 256000000000000000000), D2 := ((14671878910714285533 : Rat) / 256000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((1162081173546603 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((669503238910714285533 : Rat) / 256000000000000000000), R := ((6696662597874999998167 : Rat) / 2560000000000000000000), D0 := ((6696662597874999998167 : Rat) / 2560000000000000000000), D1 := ((2043926341874999998167 : Rat) / 2560000000000000000000), D2 := ((148348997874999998167 : Rat) / 2560000000000000000000), D3 := ((135307327732142855471 : Rat) / 1280000000000000000000), D4 := ((43326348289285688867 : Rat) / 256000000000000000000), LB := ((3285202975629939 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6696662597874999998167 : Rat) / 2560000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((53796889339285713621 : Rat) / 512000000000000000000), D4 := ((431633274124999745833 : Rat) / 2560000000000000000000), LB := ((2207646411805153 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((6699923015410714283841 : Rat) / 2560000000000000000000), D0 := ((6699923015410714283841 : Rat) / 2560000000000000000000), D1 := ((2047186759410714283841 : Rat) / 2560000000000000000000), D2 := ((151609415410714283841 : Rat) / 2560000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((1128302043469781 : Rat) / 1250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6699923015410714283841 : Rat) / 2560000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((265724029160714282431 : Rat) / 2560000000000000000000), D4 := ((428372856589285460159 : Rat) / 2560000000000000000000), LB := ((1776562925865921 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((1340636686589285713903 : Rat) / 512000000000000000000), D0 := ((1340636686589285713903 : Rat) / 512000000000000000000), D1 := ((410089435389285713903 : Rat) / 512000000000000000000), D2 := ((30973966589285713903 : Rat) / 512000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((1319660275255971 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1340636686589285713903 : Rat) / 512000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((262463611624999996757 : Rat) / 2560000000000000000000), D4 := ((85022487810714234897 : Rat) / 512000000000000000000), LB := ((7089007881140863 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((6706443850482142855189 : Rat) / 2560000000000000000000), D0 := ((6706443850482142855189 : Rat) / 2560000000000000000000), D1 := ((2053707594482142855189 : Rat) / 2560000000000000000000), D2 := ((158130250482142855189 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((1904776444443257 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6706443850482142855189 : Rat) / 2560000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((259203194089285711083 : Rat) / 2560000000000000000000), D4 := ((421852021517856888811 : Rat) / 2560000000000000000000), LB := ((18020603320748063 : Rat) / 500000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((13417778327267857138889 : Rat) / 5120000000000000000000), D0 := ((13417778327267857138889 : Rat) / 5120000000000000000000), D1 := ((4112305815267857138889 : Rat) / 5120000000000000000000), D2 := ((321151127267857138889 : Rat) / 5120000000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((3542305489390579 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13417778327267857138889 : Rat) / 5120000000000000000000), R := ((6709704268017857140863 : Rat) / 2560000000000000000000), D0 := ((6709704268017857140863 : Rat) / 2560000000000000000000), D1 := ((2056968012017857140863 : Rat) / 2560000000000000000000), D2 := ((161390668017857140863 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1024000000000000000000), D4 := ((838813416732142349111 : Rat) / 5120000000000000000000), LB := ((6394125659660577 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6709704268017857140863 : Rat) / 2560000000000000000000), R := ((13421038744803571424563 : Rat) / 5120000000000000000000), D0 := ((13421038744803571424563 : Rat) / 5120000000000000000000), D1 := ((4115566232803571424563 : Rat) / 5120000000000000000000), D2 := ((324411544803571424563 : Rat) / 5120000000000000000000), D3 := ((255942776553571425409 : Rat) / 2560000000000000000000), D4 := ((418591603982142603137 : Rat) / 2560000000000000000000), LB := ((5728098501654177 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13421038744803571424563 : Rat) / 5120000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((510255344339285707981 : Rat) / 5120000000000000000000), D4 := ((835552999196428063437 : Rat) / 5120000000000000000000), LB := ((2543328025751551 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((13424299162339285710237 : Rat) / 5120000000000000000000), D0 := ((13424299162339285710237 : Rat) / 5120000000000000000000), D1 := ((4118826650339285710237 : Rat) / 5120000000000000000000), D2 := ((327671962339285710237 : Rat) / 5120000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((2234963021658931 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13424299162339285710237 : Rat) / 5120000000000000000000), R := ((6712964685553571426537 : Rat) / 2560000000000000000000), D0 := ((6712964685553571426537 : Rat) / 2560000000000000000000), D1 := ((2060228429553571426537 : Rat) / 2560000000000000000000), D2 := ((164651085553571426537 : Rat) / 2560000000000000000000), D3 := ((506994926803571422307 : Rat) / 5120000000000000000000), D4 := ((832292581660713777763 : Rat) / 5120000000000000000000), LB := ((38780374133920437 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6712964685553571426537 : Rat) / 2560000000000000000000), R := ((13427559579874999995911 : Rat) / 5120000000000000000000), D0 := ((13427559579874999995911 : Rat) / 5120000000000000000000), D1 := ((4122087067874999995911 : Rat) / 5120000000000000000000), D2 := ((330932379874999995911 : Rat) / 5120000000000000000000), D3 := ((50536471803571427947 : Rat) / 512000000000000000000), D4 := ((415331186446428317463 : Rat) / 2560000000000000000000), LB := ((1655560157629299 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13427559579874999995911 : Rat) / 5120000000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((503734509267857136633 : Rat) / 5120000000000000000000), D4 := ((829032164124999492089 : Rat) / 5120000000000000000000), LB := ((27693061349665093 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((2686163999482142856317 : Rat) / 1024000000000000000000), D0 := ((2686163999482142856317 : Rat) / 1024000000000000000000), D1 := ((825069497082142856317 : Rat) / 1024000000000000000000), D2 := ((66838559482142856317 : Rat) / 1024000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((5631818766481389 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2686163999482142856317 : Rat) / 1024000000000000000000), R := ((6716225103089285712211 : Rat) / 2560000000000000000000), D0 := ((6716225103089285712211 : Rat) / 2560000000000000000000), D1 := ((2063488847089285712211 : Rat) / 2560000000000000000000), D2 := ((167911503089285712211 : Rat) / 2560000000000000000000), D3 := ((500474091732142850959 : Rat) / 5120000000000000000000), D4 := ((165154349317857041283 : Rat) / 1024000000000000000000), LB := ((17615183280234037 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6716225103089285712211 : Rat) / 2560000000000000000000), R := ((13434080414946428567259 : Rat) / 5120000000000000000000), D0 := ((13434080414946428567259 : Rat) / 5120000000000000000000), D1 := ((4128607902946428567259 : Rat) / 5120000000000000000000), D2 := ((337453214946428567259 : Rat) / 5120000000000000000000), D3 := ((249421941482142854061 : Rat) / 2560000000000000000000), D4 := ((412070768910714031789 : Rat) / 2560000000000000000000), LB := ((647906888485289 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13434080414946428567259 : Rat) / 5120000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1024000000000000000000), D4 := ((822511329053570920741 : Rat) / 5120000000000000000000), LB := ((8557503272746403 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((13437340832482142852933 : Rat) / 5120000000000000000000), D0 := ((13437340832482142852933 : Rat) / 5120000000000000000000), D1 := ((4131868320482142852933 : Rat) / 5120000000000000000000), D2 := ((340713632482142852933 : Rat) / 5120000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((4414657654139287 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13437340832482142852933 : Rat) / 5120000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((493953256660714279611 : Rat) / 5120000000000000000000), D4 := ((819250911517856635067 : Rat) / 5120000000000000000000), LB := ((10619841475711933 : Rat) / 2000000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((26879572291267857134377 : Rat) / 10240000000000000000000), D0 := ((26879572291267857134377 : Rat) / 10240000000000000000000), D1 := ((8268627267267857134377 : Rat) / 10240000000000000000000), D2 := ((686317891267857134377 : Rat) / 10240000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((3757756385371347 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26879572291267857134377 : Rat) / 10240000000000000000000), R := ((13440601250017857138607 : Rat) / 5120000000000000000000), D0 := ((13440601250017857138607 : Rat) / 5120000000000000000000), D1 := ((4135128738017857138607 : Rat) / 5120000000000000000000), D2 := ((343974050017857138607 : Rat) / 5120000000000000000000), D3 := ((983015887017857130711 : Rat) / 10240000000000000000000), D4 := ((1633611196732141841623 : Rat) / 10240000000000000000000), LB := ((35856996974811817 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13440601250017857138607 : Rat) / 5120000000000000000000), R := ((26882832708803571420051 : Rat) / 10240000000000000000000), D0 := ((26882832708803571420051 : Rat) / 10240000000000000000000), D1 := ((8271887684803571420051 : Rat) / 10240000000000000000000), D2 := ((689578308803571420051 : Rat) / 10240000000000000000000), D3 := ((490692839124999993937 : Rat) / 5120000000000000000000), D4 := ((815990493982142349393 : Rat) / 5120000000000000000000), LB := ((34202111918779643 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26882832708803571420051 : Rat) / 10240000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((979755469482142845037 : Rat) / 10240000000000000000000), D4 := ((1630350779196427555949 : Rat) / 10240000000000000000000), LB := ((3261308812737007 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((1075443725053571428229 : Rat) / 409600000000000000000), D0 := ((1075443725053571428229 : Rat) / 409600000000000000000), D1 := ((331005924093571428229 : Rat) / 409600000000000000000), D2 := ((27713549053571428229 : Rat) / 409600000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((1554505295843639 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1075443725053571428229 : Rat) / 409600000000000000000), R := ((13443861667553571424281 : Rat) / 5120000000000000000000), D0 := ((13443861667553571424281 : Rat) / 5120000000000000000000), D1 := ((4138389155553571424281 : Rat) / 5120000000000000000000), D2 := ((347234467553571424281 : Rat) / 5120000000000000000000), D3 := ((976495051946428559363 : Rat) / 10240000000000000000000), D4 := ((65083614466428530811 : Rat) / 409600000000000000000), LB := ((2963334648375393 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13443861667553571424281 : Rat) / 5120000000000000000000), R := ((26889353543874999991399 : Rat) / 10240000000000000000000), D0 := ((26889353543874999991399 : Rat) / 10240000000000000000000), D1 := ((8278408519874999991399 : Rat) / 10240000000000000000000), D2 := ((696099143874999991399 : Rat) / 10240000000000000000000), D3 := ((487432421589285708263 : Rat) / 5120000000000000000000), D4 := ((812730076446428063719 : Rat) / 5120000000000000000000), LB := ((176518699442213 : Rat) / 625000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26889353543874999991399 : Rat) / 10240000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((973234634410714273689 : Rat) / 10240000000000000000000), D4 := ((1623829944124998984601 : Rat) / 10240000000000000000000), LB := ((53838450344873 : Rat) / 200000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((26892613961410714277073 : Rat) / 10240000000000000000000), D0 := ((26892613961410714277073 : Rat) / 10240000000000000000000), D1 := ((8281668937410714277073 : Rat) / 10240000000000000000000), D2 := ((699359561410714277073 : Rat) / 10240000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((5132446028194293 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26892613961410714277073 : Rat) / 10240000000000000000000), R := ((2689424417017857141991 : Rat) / 1024000000000000000000), D0 := ((2689424417017857141991 : Rat) / 1024000000000000000000), D1 := ((828329914617857141991 : Rat) / 1024000000000000000000), D2 := ((70098977017857141991 : Rat) / 1024000000000000000000), D3 := ((193994843374999997603 : Rat) / 2048000000000000000000), D4 := ((1620569526589284698927 : Rat) / 10240000000000000000000), LB := ((611804789804743 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2689424417017857141991 : Rat) / 1024000000000000000000), R := ((26895874378946428562747 : Rat) / 10240000000000000000000), D0 := ((26895874378946428562747 : Rat) / 10240000000000000000000), D1 := ((8284929354946428562747 : Rat) / 10240000000000000000000), D2 := ((702619978946428562747 : Rat) / 10240000000000000000000), D3 := ((484172004053571422589 : Rat) / 5120000000000000000000), D4 := ((161893931782142755609 : Rat) / 1024000000000000000000), LB := ((11674647605619537 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26895874378946428562747 : Rat) / 10240000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((966713799339285702341 : Rat) / 10240000000000000000000), D4 := ((1617309109053570413253 : Rat) / 10240000000000000000000), LB := ((22293727598568513 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((26899134796482142848421 : Rat) / 10240000000000000000000), D0 := ((26899134796482142848421 : Rat) / 10240000000000000000000), D1 := ((8288189772482142848421 : Rat) / 10240000000000000000000), D2 := ((705880396482142848421 : Rat) / 10240000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((1065283813819623 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26899134796482142848421 : Rat) / 10240000000000000000000), R := ((13450382502624999995629 : Rat) / 5120000000000000000000), D0 := ((13450382502624999995629 : Rat) / 5120000000000000000000), D1 := ((4144909990624999995629 : Rat) / 5120000000000000000000), D2 := ((353755302624999995629 : Rat) / 5120000000000000000000), D3 := ((963453381803571416667 : Rat) / 10240000000000000000000), D4 := ((1614048691517856127579 : Rat) / 10240000000000000000000), LB := ((5096332423525779 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13450382502624999995629 : Rat) / 5120000000000000000000), R := ((5380479042803571426819 : Rat) / 2048000000000000000000), D0 := ((5380479042803571426819 : Rat) / 2048000000000000000000), D1 := ((1658290038003571426819 : Rat) / 2048000000000000000000), D2 := ((141828162803571426819 : Rat) / 2048000000000000000000), D3 := ((96182317303571427383 : Rat) / 1024000000000000000000), D4 := ((806209241374999492371 : Rat) / 5120000000000000000000), LB := ((3906575446955829 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5380479042803571426819 : Rat) / 2048000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((960192964267857130993 : Rat) / 10240000000000000000000), D4 := ((322157654796428368381 : Rat) / 2048000000000000000000), LB := ((468712730530077 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((26905655631553571419769 : Rat) / 10240000000000000000000), D0 := ((26905655631553571419769 : Rat) / 10240000000000000000000), D1 := ((8294710607553571419769 : Rat) / 10240000000000000000000), D2 := ((712401231553571419769 : Rat) / 10240000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((18032416922261763 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26905655631553571419769 : Rat) / 10240000000000000000000), R := ((13453642920160714281303 : Rat) / 5120000000000000000000), D0 := ((13453642920160714281303 : Rat) / 5120000000000000000000), D1 := ((4148170408160714281303 : Rat) / 5120000000000000000000), D2 := ((357015720160714281303 : Rat) / 5120000000000000000000), D3 := ((956932546732142845319 : Rat) / 10240000000000000000000), D4 := ((1607527856446427556231 : Rat) / 10240000000000000000000), LB := ((8692396279484649 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13453642920160714281303 : Rat) / 5120000000000000000000), R := ((26908916049089285705443 : Rat) / 10240000000000000000000), D0 := ((26908916049089285705443 : Rat) / 10240000000000000000000), D1 := ((8297971025089285705443 : Rat) / 10240000000000000000000), D2 := ((715661649089285705443 : Rat) / 10240000000000000000000), D3 := ((477651168982142851241 : Rat) / 5120000000000000000000), D4 := ((802948823839285206697 : Rat) / 5120000000000000000000), LB := ((525182165968599 : Rat) / 3125000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26908916049089285705443 : Rat) / 10240000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((190734425839285711929 : Rat) / 2048000000000000000000), D4 := ((1604267438910713270557 : Rat) / 10240000000000000000000), LB := ((8147860661385231 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((26912176466624999991117 : Rat) / 10240000000000000000000), D0 := ((26912176466624999991117 : Rat) / 10240000000000000000000), D1 := ((8301231442624999991117 : Rat) / 10240000000000000000000), D2 := ((718922066624999991117 : Rat) / 10240000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((7927331855181463 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26912176466624999991117 : Rat) / 10240000000000000000000), R := ((13456903337696428566977 : Rat) / 5120000000000000000000), D0 := ((13456903337696428566977 : Rat) / 5120000000000000000000), D1 := ((4151430825696428566977 : Rat) / 5120000000000000000000), D2 := ((360276137696428566977 : Rat) / 5120000000000000000000), D3 := ((950411711660714273971 : Rat) / 10240000000000000000000), D4 := ((1601007021374998984883 : Rat) / 10240000000000000000000), LB := ((15482852567375027 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13456903337696428566977 : Rat) / 5120000000000000000000), R := ((26915436884160714276791 : Rat) / 10240000000000000000000), D0 := ((26915436884160714276791 : Rat) / 10240000000000000000000), D1 := ((8304491860160714276791 : Rat) / 10240000000000000000000), D2 := ((722182484160714276791 : Rat) / 10240000000000000000000), D3 := ((474390751446428565567 : Rat) / 5120000000000000000000), D4 := ((799688406303570921023 : Rat) / 5120000000000000000000), LB := ((15180484971966113 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26915436884160714276791 : Rat) / 10240000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((947151294124999988297 : Rat) / 10240000000000000000000), D4 := ((1597746603839284699209 : Rat) / 10240000000000000000000), LB := ((7473879496627811 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((5383739460339285712493 : Rat) / 2048000000000000000000), D0 := ((5383739460339285712493 : Rat) / 2048000000000000000000), D1 := ((1661550455539285712493 : Rat) / 2048000000000000000000), D2 := ((145088580339285712493 : Rat) / 2048000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((1478487369803161 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5383739460339285712493 : Rat) / 2048000000000000000000), R := ((13460163755232142852651 : Rat) / 5120000000000000000000), D0 := ((13460163755232142852651 : Rat) / 5120000000000000000000), D1 := ((4154691243232142852651 : Rat) / 5120000000000000000000), D2 := ((363536555232142852651 : Rat) / 5120000000000000000000), D3 := ((943890876589285702623 : Rat) / 10240000000000000000000), D4 := ((318897237260714082707 : Rat) / 2048000000000000000000), LB := ((3673007289306529 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13460163755232142852651 : Rat) / 5120000000000000000000), R := ((26921957719232142848139 : Rat) / 10240000000000000000000), D0 := ((26921957719232142848139 : Rat) / 10240000000000000000000), D1 := ((8311012695232142848139 : Rat) / 10240000000000000000000), D2 := ((728703319232142848139 : Rat) / 10240000000000000000000), D3 := ((471130333910714279893 : Rat) / 5120000000000000000000), D4 := ((796427988767856635349 : Rat) / 5120000000000000000000), LB := ((14669426453003953 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26921957719232142848139 : Rat) / 10240000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((940630459053571416949 : Rat) / 10240000000000000000000), D4 := ((1591225768767856127861 : Rat) / 10240000000000000000000), LB := ((3679316921370579 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((26925218136767857133813 : Rat) / 10240000000000000000000), D0 := ((26925218136767857133813 : Rat) / 10240000000000000000000), D1 := ((8314273112767857133813 : Rat) / 10240000000000000000000), D2 := ((731963736767857133813 : Rat) / 10240000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((741787798963639 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26925218136767857133813 : Rat) / 10240000000000000000000), R := ((538536966910714285533 : Rat) / 204800000000000000000), D0 := ((538536966910714285533 : Rat) / 204800000000000000000), D1 := ((166318066430714285533 : Rat) / 204800000000000000000), D2 := ((14671878910714285533 : Rat) / 204800000000000000000), D3 := ((37494801660714285251 : Rat) / 409600000000000000000), D4 := ((1587965351232141842187 : Rat) / 10240000000000000000000), LB := ((7512547745520959 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((538536966910714285533 : Rat) / 204800000000000000000), R := ((26928478554303571419487 : Rat) / 10240000000000000000000), D0 := ((26928478554303571419487 : Rat) / 10240000000000000000000), D1 := ((8317533530303571419487 : Rat) / 10240000000000000000000), D2 := ((735224154303571419487 : Rat) / 10240000000000000000000), D3 := ((467869916374999994219 : Rat) / 5120000000000000000000), D4 := ((31726702849285693987 : Rat) / 204800000000000000000), LB := ((1910686426987579 : Rat) / 12500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26928478554303571419487 : Rat) / 10240000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((934109623982142845601 : Rat) / 10240000000000000000000), D4 := ((1584704933696427556513 : Rat) / 10240000000000000000000), LB := ((15617149994984203 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((26931738971839285705161 : Rat) / 10240000000000000000000), D0 := ((26931738971839285705161 : Rat) / 10240000000000000000000), D1 := ((8320793947839285705161 : Rat) / 10240000000000000000000), D2 := ((738484571839285705161 : Rat) / 10240000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((16020278522010933 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26931738971839285705161 : Rat) / 10240000000000000000000), R := ((13466684590303571423999 : Rat) / 5120000000000000000000), D0 := ((13466684590303571423999 : Rat) / 5120000000000000000000), D1 := ((4161212078303571423999 : Rat) / 5120000000000000000000), D2 := ((370057390303571423999 : Rat) / 5120000000000000000000), D3 := ((930849206446428559927 : Rat) / 10240000000000000000000), D4 := ((1581444516160713270839 : Rat) / 10240000000000000000000), LB := ((412377133776759 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13466684590303571423999 : Rat) / 5120000000000000000000), R := ((5386999877874999998167 : Rat) / 2048000000000000000000), D0 := ((5386999877874999998167 : Rat) / 2048000000000000000000), D1 := ((1664810873074999998167 : Rat) / 2048000000000000000000), D2 := ((148348997874999998167 : Rat) / 2048000000000000000000), D3 := ((92921899767857141709 : Rat) / 1024000000000000000000), D4 := ((789907153696428064001 : Rat) / 5120000000000000000000), LB := ((17041779903356757 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5386999877874999998167 : Rat) / 2048000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((927588788910714274253 : Rat) / 10240000000000000000000), D4 := ((315636819724999797033 : Rat) / 2048000000000000000000), LB := ((883028633724553 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((26938259806910714276509 : Rat) / 10240000000000000000000), D0 := ((26938259806910714276509 : Rat) / 10240000000000000000000), D1 := ((8327314782910714276509 : Rat) / 10240000000000000000000), D2 := ((745005406910714276509 : Rat) / 10240000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((18351675242575527 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26938259806910714276509 : Rat) / 10240000000000000000000), R := ((13469945007839285709673 : Rat) / 5120000000000000000000), D0 := ((13469945007839285709673 : Rat) / 5120000000000000000000), D1 := ((4164472495839285709673 : Rat) / 5120000000000000000000), D2 := ((373317807839285709673 : Rat) / 5120000000000000000000), D3 := ((924328371374999988579 : Rat) / 10240000000000000000000), D4 := ((1574923681089284699491 : Rat) / 10240000000000000000000), LB := ((764612010982213 : Rat) / 4000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13469945007839285709673 : Rat) / 5120000000000000000000), R := ((26941520224446428562183 : Rat) / 10240000000000000000000), D0 := ((26941520224446428562183 : Rat) / 10240000000000000000000), D1 := ((8330575200446428562183 : Rat) / 10240000000000000000000), D2 := ((748265824446428562183 : Rat) / 10240000000000000000000), D3 := ((461349081303571422871 : Rat) / 5120000000000000000000), D4 := ((786646736160713778327 : Rat) / 5120000000000000000000), LB := ((9975830767339211 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26941520224446428562183 : Rat) / 10240000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((184213590767857140581 : Rat) / 2048000000000000000000), D4 := ((1571663263553570413817 : Rat) / 10240000000000000000000), LB := ((20860973891492773 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((26944780641982142847857 : Rat) / 10240000000000000000000), D0 := ((26944780641982142847857 : Rat) / 10240000000000000000000), D1 := ((8333835617982142847857 : Rat) / 10240000000000000000000), D2 := ((751526241982142847857 : Rat) / 10240000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((21843453325437467 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26944780641982142847857 : Rat) / 10240000000000000000000), R := ((13473205425374999995347 : Rat) / 5120000000000000000000), D0 := ((13473205425374999995347 : Rat) / 5120000000000000000000), D1 := ((4167732913374999995347 : Rat) / 5120000000000000000000), D2 := ((376578225374999995347 : Rat) / 5120000000000000000000), D3 := ((917807536303571417231 : Rat) / 10240000000000000000000), D4 := ((1568402846017856128143 : Rat) / 10240000000000000000000), LB := ((11449658468493107 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13473205425374999995347 : Rat) / 5120000000000000000000), R := ((26948041059517857133531 : Rat) / 10240000000000000000000), D0 := ((26948041059517857133531 : Rat) / 10240000000000000000000), D1 := ((8337096035517857133531 : Rat) / 10240000000000000000000), D2 := ((754786659517857133531 : Rat) / 10240000000000000000000), D3 := ((458088663767857137197 : Rat) / 5120000000000000000000), D4 := ((783386318624999492653 : Rat) / 5120000000000000000000), LB := ((300359786924477 : Rat) / 1250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26948041059517857133531 : Rat) / 10240000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((914547118767857131557 : Rat) / 10240000000000000000000), D4 := ((1565142428482141842469 : Rat) / 10240000000000000000000), LB := ((2523207073976963 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((5390260295410714283841 : Rat) / 2048000000000000000000), D0 := ((5390260295410714283841 : Rat) / 2048000000000000000000), D1 := ((1668071290610714283841 : Rat) / 2048000000000000000000), D2 := ((151609415410714283841 : Rat) / 2048000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((26509400800722727 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5390260295410714283841 : Rat) / 2048000000000000000000), R := ((13476465842910714281021 : Rat) / 5120000000000000000000), D0 := ((13476465842910714281021 : Rat) / 5120000000000000000000), D1 := ((4170993330910714281021 : Rat) / 5120000000000000000000), D2 := ((379838642910714281021 : Rat) / 5120000000000000000000), D3 := ((911286701232142845883 : Rat) / 10240000000000000000000), D4 := ((312376402189285511359 : Rat) / 2048000000000000000000), LB := ((2786099479458459 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13476465842910714281021 : Rat) / 5120000000000000000000), R := ((26954561894589285704879 : Rat) / 10240000000000000000000), D0 := ((26954561894589285704879 : Rat) / 10240000000000000000000), D1 := ((8343616870589285704879 : Rat) / 10240000000000000000000), D2 := ((761307494589285704879 : Rat) / 10240000000000000000000), D3 := ((454828246232142851523 : Rat) / 5120000000000000000000), D4 := ((780125901089285206979 : Rat) / 5120000000000000000000), LB := ((2928707553839227 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26954561894589285704879 : Rat) / 10240000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((908026283696428560209 : Rat) / 10240000000000000000000), D4 := ((1558621593410713271121 : Rat) / 10240000000000000000000), LB := ((3078786701633529 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((26957822312124999990553 : Rat) / 10240000000000000000000), D0 := ((26957822312124999990553 : Rat) / 10240000000000000000000), D1 := ((8346877288124999990553 : Rat) / 10240000000000000000000), D2 := ((764567912124999990553 : Rat) / 10240000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((809089859711079 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26957822312124999990553 : Rat) / 10240000000000000000000), R := ((2695945252089285713339 : Rat) / 1024000000000000000000), D0 := ((2695945252089285713339 : Rat) / 1024000000000000000000), D1 := ((834850749689285713339 : Rat) / 1024000000000000000000), D2 := ((76619812089285713339 : Rat) / 1024000000000000000000), D3 := ((180953173232142854907 : Rat) / 2048000000000000000000), D4 := ((1555361175874998985447 : Rat) / 10240000000000000000000), LB := ((34014483998257017 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2695945252089285713339 : Rat) / 1024000000000000000000), R := ((26961082729660714276227 : Rat) / 10240000000000000000000), D0 := ((26961082729660714276227 : Rat) / 10240000000000000000000), D1 := ((8350137705660714276227 : Rat) / 10240000000000000000000), D2 := ((767828329660714276227 : Rat) / 10240000000000000000000), D3 := ((451567828696428565849 : Rat) / 5120000000000000000000), D4 := ((155373096710714184261 : Rat) / 1024000000000000000000), LB := ((3574076338143939 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26961082729660714276227 : Rat) / 10240000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((901505448624999988861 : Rat) / 10240000000000000000000), D4 := ((1552100758339284699773 : Rat) / 10240000000000000000000), LB := ((1877133063720171 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((26964343147196428561901 : Rat) / 10240000000000000000000), D0 := ((26964343147196428561901 : Rat) / 10240000000000000000000), D1 := ((8353398123196428561901 : Rat) / 10240000000000000000000), D2 := ((771088747196428561901 : Rat) / 10240000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((61594386910023 : Rat) / 156250000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26964343147196428561901 : Rat) / 10240000000000000000000), R := ((13482986677982142852369 : Rat) / 5120000000000000000000), D0 := ((13482986677982142852369 : Rat) / 5120000000000000000000), D1 := ((4177514165982142852369 : Rat) / 5120000000000000000000), D2 := ((386359477982142852369 : Rat) / 5120000000000000000000), D3 := ((898245031089285703187 : Rat) / 10240000000000000000000), D4 := ((1548840340803570414099 : Rat) / 10240000000000000000000), LB := ((20687116794085303 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13482986677982142852369 : Rat) / 5120000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((17932296446428571207 : Rat) / 204800000000000000000), D4 := ((773605066017856635631 : Rat) / 5120000000000000000000), LB := ((389877237901709 : Rat) / 12500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((13486247095517857138043 : Rat) / 5120000000000000000000), D0 := ((13486247095517857138043 : Rat) / 5120000000000000000000), D1 := ((4180774583517857138043 : Rat) / 5120000000000000000000), D2 := ((389619895517857138043 : Rat) / 5120000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((385987428624999746397 : Rat) / 2560000000000000000000), LB := ((3711624507318767 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13486247095517857138043 : Rat) / 5120000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((445046993624999994501 : Rat) / 5120000000000000000000), D4 := ((770344648482142349957 : Rat) / 5120000000000000000000), LB := ((12035537272819807 : Rat) / 100000000000000000000) }
]

def block189RightChunk000L : Rat := ((8901658482142857151 : Rat) / 5000000000000000000)
def block189RightChunk000R : Rat := ((168598466303571428511 : Rat) / 64000000000000000000)

def block189RightChunk000Certificate : Bool :=
  allBoxesValid block189RightChunk000 &&
  coversFromBool block189RightChunk000 block189RightChunk000L block189RightChunk000R

theorem block189RightChunk000Certificate_eq_true :
    block189RightChunk000Certificate = true := by
  native_decide

def block189RightChunk001 : List RatBox := [
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((13489507513053571423717 : Rat) / 5120000000000000000000), D0 := ((13489507513053571423717 : Rat) / 5120000000000000000000), D1 := ((4184035001053571423717 : Rat) / 5120000000000000000000), D2 := ((392880313053571423717 : Rat) / 5120000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((3391557368304099 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13489507513053571423717 : Rat) / 5120000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((441786576089285708827 : Rat) / 5120000000000000000000), D4 := ((767084230946428064283 : Rat) / 5120000000000000000000), LB := ((2219192235833889 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((13492767930589285709391 : Rat) / 5120000000000000000000), D0 := ((13492767930589285709391 : Rat) / 5120000000000000000000), D1 := ((4187295418589285709391 : Rat) / 5120000000000000000000), D2 := ((396140730589285709391 : Rat) / 5120000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((382727011089285460723 : Rat) / 2560000000000000000000), LB := ((1386994461506641 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13492767930589285709391 : Rat) / 5120000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((438526158553571423153 : Rat) / 5120000000000000000000), D4 := ((763823813410713778609 : Rat) / 5120000000000000000000), LB := ((3360365393363929 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((2699205669624999999013 : Rat) / 1024000000000000000000), D0 := ((2699205669624999999013 : Rat) / 1024000000000000000000), D1 := ((838111167224999999013 : Rat) / 1024000000000000000000), D2 := ((79880229624999999013 : Rat) / 1024000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((397852043216379 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2699205669624999999013 : Rat) / 1024000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((435265741017857137479 : Rat) / 5120000000000000000000), D4 := ((152112679174999898587 : Rat) / 1024000000000000000000), LB := ((231432749675603 : Rat) / 500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((13499288765660714280739 : Rat) / 5120000000000000000000), D0 := ((13499288765660714280739 : Rat) / 5120000000000000000000), D1 := ((4193816253660714280739 : Rat) / 5120000000000000000000), D2 := ((402661565660714280739 : Rat) / 5120000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((379466593553571175049 : Rat) / 2560000000000000000000), LB := ((2655486116037581 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13499288765660714280739 : Rat) / 5120000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((86401064696428570361 : Rat) / 1024000000000000000000), D4 := ((757302978339285207261 : Rat) / 5120000000000000000000), LB := ((3012838767714049 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((13502549183196428566413 : Rat) / 5120000000000000000000), D0 := ((13502549183196428566413 : Rat) / 5120000000000000000000), D1 := ((4197076671196428566413 : Rat) / 5120000000000000000000), D2 := ((405921983196428566413 : Rat) / 5120000000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((6772978557046117 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13502549183196428566413 : Rat) / 5120000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((428744905946428566131 : Rat) / 5120000000000000000000), D4 := ((754042560803570921587 : Rat) / 5120000000000000000000), LB := ((188827131246877 : Rat) / 250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((601929881628571023 : Rat) / 4096000000000000000), LB := ((3476837099791741 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((2079421387108371 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((372945758482142603701 : Rat) / 2560000000000000000000), LB := ((7891659801629869 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((1487173804255587 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((369685340946428318027 : Rat) / 2560000000000000000000), LB := ((1617968831125749 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((5185572826309909 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((366424923410714032353 : Rat) / 2560000000000000000000), LB := ((3198628017925531 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((192023757100597 : Rat) / 125000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((363164505874999746679 : Rat) / 2560000000000000000000), LB := ((4518828626645377 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((5007728689162827 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((11205347054763781 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((2252635043468107 : Rat) / 1250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((12736609488218087 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((2098811282416381 : Rat) / 625000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((5378573940295617 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((3052426951550641 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((10652952134133753 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((7918402329771701 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((4610719728452117 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((581952021256453 : Rat) / 50000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((1011135459550179 : Rat) / 125000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((1630494338452143 : Rat) / 200000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((5244060637203893 : Rat) / 50000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((136792435223214285659 : Rat) / 50000000000000000000), D0 := ((136792435223214285659 : Rat) / 50000000000000000000), D1 := ((45918680223214285659 : Rat) / 50000000000000000000), D2 := ((8895685223214285659 : Rat) / 50000000000000000000), D3 := ((372320691964285737 : Rat) / 25000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((47739740856487 : Rat) / 312500000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((136792435223214285659 : Rat) / 50000000000000000000), R := ((137537076607142857133 : Rat) / 50000000000000000000), D0 := ((137537076607142857133 : Rat) / 50000000000000000000), D1 := ((46663321607142857133 : Rat) / 50000000000000000000), D2 := ((9640326607142857133 : Rat) / 50000000000000000000), D3 := ((372320691964285737 : Rat) / 12500000000000000000), D4 := ((2432093526785709341 : Rat) / 50000000000000000000), LB := ((4000202162488653 : Rat) / 200000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((137537076607142857133 : Rat) / 50000000000000000000), R := ((275446473906250000003 : Rat) / 100000000000000000000), D0 := ((275446473906250000003 : Rat) / 100000000000000000000), D1 := ((93698963906250000003 : Rat) / 100000000000000000000), D2 := ((19652973906250000003 : Rat) / 100000000000000000000), D3 := ((3350886227678571633 : Rat) / 100000000000000000000), D4 := ((1687452142857137867 : Rat) / 50000000000000000000), LB := ((6169812933067731 : Rat) / 250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275446473906250000003 : Rat) / 100000000000000000000), R := ((13790939729910714287 : Rat) / 5000000000000000000), D0 := ((13790939729910714287 : Rat) / 5000000000000000000), D1 := ((4703564229910714287 : Rat) / 5000000000000000000), D2 := ((1001264729910714287 : Rat) / 5000000000000000000), D3 := ((372320691964285737 : Rat) / 10000000000000000000), D4 := ((3002583593749989997 : Rat) / 100000000000000000000), LB := ((336768054642389 : Rat) / 40000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13790939729910714287 : Rat) / 5000000000000000000), R := ((552009909888392857217 : Rat) / 200000000000000000000), D0 := ((552009909888392857217 : Rat) / 200000000000000000000), D1 := ((188514889888392857217 : Rat) / 200000000000000000000), D2 := ((40422909888392857217 : Rat) / 200000000000000000000), D3 := ((7818734531250000477 : Rat) / 200000000000000000000), D4 := ((131513145089285213 : Rat) / 5000000000000000000), LB := ((7892746905715453 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552009909888392857217 : Rat) / 200000000000000000000), R := ((276191115290178571477 : Rat) / 100000000000000000000), D0 := ((276191115290178571477 : Rat) / 100000000000000000000), D1 := ((94443605290178571477 : Rat) / 100000000000000000000), D2 := ((20397615290178571477 : Rat) / 100000000000000000000), D3 := ((4095527611607143107 : Rat) / 100000000000000000000), D4 := ((4888205111607122783 : Rat) / 200000000000000000000), LB := ((4556792062983317 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276191115290178571477 : Rat) / 100000000000000000000), R := ((221027356370535714329 : Rat) / 80000000000000000000), D0 := ((221027356370535714329 : Rat) / 80000000000000000000), D1 := ((75629348370535714329 : Rat) / 80000000000000000000), D2 := ((16392556370535714329 : Rat) / 80000000000000000000), D3 := ((3350886227678571633 : Rat) / 80000000000000000000), D4 := ((2257942209821418523 : Rat) / 100000000000000000000), LB := ((143228440165597 : Rat) / 40000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221027356370535714329 : Rat) / 80000000000000000000), R := ((552754551272321428691 : Rat) / 200000000000000000000), D0 := ((552754551272321428691 : Rat) / 200000000000000000000), D1 := ((189259531272321428691 : Rat) / 200000000000000000000), D2 := ((41167551272321428691 : Rat) / 200000000000000000000), D3 := ((8563375915178571951 : Rat) / 200000000000000000000), D4 := ((1731889629464277671 : Rat) / 80000000000000000000), LB := ((15104093075344327 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552754551272321428691 : Rat) / 200000000000000000000), R := ((2211390525781250000501 : Rat) / 800000000000000000000), D0 := ((2211390525781250000501 : Rat) / 800000000000000000000), D1 := ((757410445781250000501 : Rat) / 800000000000000000000), D2 := ((165042525781250000501 : Rat) / 800000000000000000000), D3 := ((34625824352678573541 : Rat) / 800000000000000000000), D4 := ((4143563727678551309 : Rat) / 200000000000000000000), LB := ((26436472517887277 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2211390525781250000501 : Rat) / 800000000000000000000), R := ((1105881423236607143119 : Rat) / 400000000000000000000), D0 := ((1105881423236607143119 : Rat) / 400000000000000000000), D1 := ((378891383236607143119 : Rat) / 400000000000000000000), D2 := ((82707423236607143119 : Rat) / 400000000000000000000), D3 := ((17499072522321429639 : Rat) / 400000000000000000000), D4 := ((16201934218749919499 : Rat) / 800000000000000000000), LB := ((1818136898558309 : Rat) / 1000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1105881423236607143119 : Rat) / 400000000000000000000), R := ((88485406686607142879 : Rat) / 32000000000000000000), D0 := ((88485406686607142879 : Rat) / 32000000000000000000), D1 := ((30326203486607142879 : Rat) / 32000000000000000000), D2 := ((6631486686607142879 : Rat) / 32000000000000000000), D3 := ((7074093147321429003 : Rat) / 160000000000000000000), D4 := ((7914806763392816881 : Rat) / 400000000000000000000), LB := ((53129579429681 : Rat) / 50000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((88485406686607142879 : Rat) / 32000000000000000000), R := ((138281717991071428607 : Rat) / 50000000000000000000), D0 := ((138281717991071428607 : Rat) / 50000000000000000000), D1 := ((47407962991071428607 : Rat) / 50000000000000000000), D2 := ((10384967991071428607 : Rat) / 50000000000000000000), D3 := ((1116962075892857211 : Rat) / 25000000000000000000), D4 := ((618291713392853921 : Rat) / 32000000000000000000), LB := ((3789310530510903 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138281717991071428607 : Rat) / 50000000000000000000), R := ((4425387296406250001161 : Rat) / 1600000000000000000000), D0 := ((4425387296406250001161 : Rat) / 1600000000000000000000), D1 := ((1517427136406250001161 : Rat) / 1600000000000000000000), D2 := ((332691296406250001161 : Rat) / 1600000000000000000000), D3 := ((71857893549107147241 : Rat) / 1600000000000000000000), D4 := ((942810758928566393 : Rat) / 50000000000000000000), LB := ((12086682423896877 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4425387296406250001161 : Rat) / 1600000000000000000000), R := ((2212879808549107143449 : Rat) / 800000000000000000000), D0 := ((2212879808549107143449 : Rat) / 800000000000000000000), D1 := ((758899728549107143449 : Rat) / 800000000000000000000), D2 := ((166531808549107143449 : Rat) / 800000000000000000000), D3 := ((36115107120535716489 : Rat) / 800000000000000000000), D4 := ((29797623593749838839 : Rat) / 1600000000000000000000), LB := ((1854847091295353 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2212879808549107143449 : Rat) / 800000000000000000000), R := ((885226387558035714527 : Rat) / 320000000000000000000), D0 := ((885226387558035714527 : Rat) / 320000000000000000000), D1 := ((303634355558035714527 : Rat) / 320000000000000000000), D2 := ((66687187558035714527 : Rat) / 320000000000000000000), D3 := ((14520506986607143743 : Rat) / 320000000000000000000), D4 := ((14712651450892776551 : Rat) / 800000000000000000000), LB := ((6656057345040267 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((885226387558035714527 : Rat) / 320000000000000000000), R := ((1106626064620535714593 : Rat) / 400000000000000000000), D0 := ((1106626064620535714593 : Rat) / 400000000000000000000), D1 := ((379636024620535714593 : Rat) / 400000000000000000000), D2 := ((83452064620535714593 : Rat) / 400000000000000000000), D3 := ((18243713906250001113 : Rat) / 400000000000000000000), D4 := ((5810596441964253473 : Rat) / 320000000000000000000), LB := ((42353659946270383 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106626064620535714593 : Rat) / 400000000000000000000), R := ((4426876579174107144109 : Rat) / 1600000000000000000000), D0 := ((4426876579174107144109 : Rat) / 1600000000000000000000), D1 := ((1518916419174107144109 : Rat) / 1600000000000000000000), D2 := ((334180579174107144109 : Rat) / 1600000000000000000000), D3 := ((73347176316964290189 : Rat) / 1600000000000000000000), D4 := ((7170165379464245407 : Rat) / 400000000000000000000), LB := ((20155295645007953 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4426876579174107144109 : Rat) / 1600000000000000000000), R := ((1770825095808035714791 : Rat) / 640000000000000000000), D0 := ((1770825095808035714791 : Rat) / 640000000000000000000), D1 := ((607641031808035714791 : Rat) / 640000000000000000000), D2 := ((133746695808035714791 : Rat) / 640000000000000000000), D3 := ((29413334665178573223 : Rat) / 640000000000000000000), D4 := ((28308340825892695891 : Rat) / 1600000000000000000000), LB := ((886919748389961 : Rat) / 1250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1770825095808035714791 : Rat) / 640000000000000000000), R := ((2213624449933035714923 : Rat) / 800000000000000000000), D0 := ((2213624449933035714923 : Rat) / 800000000000000000000), D1 := ((759644369933035714923 : Rat) / 800000000000000000000), D2 := ((167276449933035714923 : Rat) / 800000000000000000000), D3 := ((36859748504464287963 : Rat) / 800000000000000000000), D4 := ((11248872191964221209 : Rat) / 640000000000000000000), LB := ((1230745799662647 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2213624449933035714923 : Rat) / 800000000000000000000), R := ((8854870120424107145429 : Rat) / 3200000000000000000000), D0 := ((8854870120424107145429 : Rat) / 3200000000000000000000), D1 := ((3038949800424107145429 : Rat) / 3200000000000000000000), D2 := ((669478120424107145429 : Rat) / 3200000000000000000000), D3 := ((147811314709821437589 : Rat) / 3200000000000000000000), D4 := ((13968010066964205077 : Rat) / 800000000000000000000), LB := ((5264650041854613 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8854870120424107145429 : Rat) / 3200000000000000000000), R := ((4427621220558035715583 : Rat) / 1600000000000000000000), D0 := ((4427621220558035715583 : Rat) / 1600000000000000000000), D1 := ((1519661060558035715583 : Rat) / 1600000000000000000000), D2 := ((334925220558035715583 : Rat) / 1600000000000000000000), D3 := ((74091817700892861663 : Rat) / 1600000000000000000000), D4 := ((55499719575892534571 : Rat) / 3200000000000000000000), LB := ((885721841139997 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4427621220558035715583 : Rat) / 1600000000000000000000), R := ((8855614761808035716903 : Rat) / 3200000000000000000000), D0 := ((8855614761808035716903 : Rat) / 3200000000000000000000), D1 := ((3039694441808035716903 : Rat) / 3200000000000000000000), D2 := ((670222761808035716903 : Rat) / 3200000000000000000000), D3 := ((148555956093750009063 : Rat) / 3200000000000000000000), D4 := ((27563699441964124417 : Rat) / 1600000000000000000000), LB := ((9115264916341459 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8855614761808035716903 : Rat) / 3200000000000000000000), R := ((110699838531250000033 : Rat) / 40000000000000000000), D0 := ((110699838531250000033 : Rat) / 40000000000000000000), D1 := ((38000834531250000033 : Rat) / 40000000000000000000), D2 := ((8382438531250000033 : Rat) / 40000000000000000000), D3 := ((372320691964285737 : Rat) / 8000000000000000000), D4 := ((54755078191963963097 : Rat) / 3200000000000000000000), LB := ((116706059121241 : Rat) / 400000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110699838531250000033 : Rat) / 40000000000000000000), R := ((8856359403191964288377 : Rat) / 3200000000000000000000), D0 := ((8856359403191964288377 : Rat) / 3200000000000000000000), D1 := ((3040439083191964288377 : Rat) / 3200000000000000000000), D2 := ((670967403191964288377 : Rat) / 3200000000000000000000), D3 := ((149300597477678580537 : Rat) / 3200000000000000000000), D4 := ((679784468749995967 : Rat) / 40000000000000000000), LB := ((701177771506023 : Rat) / 3125000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8856359403191964288377 : Rat) / 3200000000000000000000), R := ((4428365861941964287057 : Rat) / 1600000000000000000000), D0 := ((4428365861941964287057 : Rat) / 1600000000000000000000), D1 := ((1520405701941964287057 : Rat) / 1600000000000000000000), D2 := ((335669861941964287057 : Rat) / 1600000000000000000000), D3 := ((74836459084821433137 : Rat) / 1600000000000000000000), D4 := ((54010436808035391623 : Rat) / 3200000000000000000000), LB := ((16249935506484903 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4428365861941964287057 : Rat) / 1600000000000000000000), R := ((8857104044575892859851 : Rat) / 3200000000000000000000), D0 := ((8857104044575892859851 : Rat) / 3200000000000000000000), D1 := ((3041183724575892859851 : Rat) / 3200000000000000000000), D2 := ((671712044575892859851 : Rat) / 3200000000000000000000), D3 := ((150045238861607152011 : Rat) / 3200000000000000000000), D4 := ((26819058058035552943 : Rat) / 1600000000000000000000), LB := ((2654683842309713 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8857104044575892859851 : Rat) / 3200000000000000000000), R := ((2214369091316964286397 : Rat) / 800000000000000000000), D0 := ((2214369091316964286397 : Rat) / 800000000000000000000), D1 := ((760389011316964286397 : Rat) / 800000000000000000000), D2 := ((168021091316964286397 : Rat) / 800000000000000000000), D3 := ((37604389888392859437 : Rat) / 800000000000000000000), D4 := ((53265795424106820149 : Rat) / 3200000000000000000000), LB := ((5549697721568547 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2214369091316964286397 : Rat) / 800000000000000000000), R := ((354313947438392857253 : Rat) / 128000000000000000000), D0 := ((354313947438392857253 : Rat) / 128000000000000000000), D1 := ((121677134638392857253 : Rat) / 128000000000000000000), D2 := ((26898267438392857253 : Rat) / 128000000000000000000), D3 := ((30157976049107144697 : Rat) / 640000000000000000000), D4 := ((13223368683035633603 : Rat) / 800000000000000000000), LB := ((1048564728339807 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((354313947438392857253 : Rat) / 128000000000000000000), R := ((17716069692611607148387 : Rat) / 6400000000000000000000), D0 := ((17716069692611607148387 : Rat) / 6400000000000000000000), D1 := ((6084229052611607148387 : Rat) / 6400000000000000000000), D2 := ((1345285692611607148387 : Rat) / 6400000000000000000000), D3 := ((301952081183035732707 : Rat) / 6400000000000000000000), D4 := ((2100846161607129947 : Rat) / 128000000000000000000), LB := ((3201183612895897 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17716069692611607148387 : Rat) / 6400000000000000000000), R := ((4429110503325892858531 : Rat) / 1600000000000000000000), D0 := ((4429110503325892858531 : Rat) / 1600000000000000000000), D1 := ((1521150343325892858531 : Rat) / 1600000000000000000000), D2 := ((336414503325892858531 : Rat) / 1600000000000000000000), D3 := ((75581100468750004611 : Rat) / 1600000000000000000000), D4 := ((104669987388392211613 : Rat) / 6400000000000000000000), LB := ((6047473647358137 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4429110503325892858531 : Rat) / 1600000000000000000000), R := ((17716814333995535719861 : Rat) / 6400000000000000000000), D0 := ((17716814333995535719861 : Rat) / 6400000000000000000000), D1 := ((6084973693995535719861 : Rat) / 6400000000000000000000), D2 := ((1346030333995535719861 : Rat) / 6400000000000000000000), D3 := ((302696722566964304181 : Rat) / 6400000000000000000000), D4 := ((26074416674106981469 : Rat) / 1600000000000000000000), LB := ((5721736180419601 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17716814333995535719861 : Rat) / 6400000000000000000000), R := ((8858593327343750002799 : Rat) / 3200000000000000000000), D0 := ((8858593327343750002799 : Rat) / 3200000000000000000000), D1 := ((3042673007343750002799 : Rat) / 3200000000000000000000), D2 := ((673201327343750002799 : Rat) / 3200000000000000000000), D3 := ((151534521629464294959 : Rat) / 3200000000000000000000), D4 := ((103925346004463640139 : Rat) / 6400000000000000000000), LB := ((27126548644063053 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8858593327343750002799 : Rat) / 3200000000000000000000), R := ((3543511795075892858267 : Rat) / 1280000000000000000000), D0 := ((3543511795075892858267 : Rat) / 1280000000000000000000), D1 := ((1217143667075892858267 : Rat) / 1280000000000000000000), D2 := ((269354995075892858267 : Rat) / 1280000000000000000000), D3 := ((60688272790178575131 : Rat) / 1280000000000000000000), D4 := ((51776512656249677201 : Rat) / 3200000000000000000000), LB := ((805992350180057 : Rat) / 3125000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3543511795075892858267 : Rat) / 1280000000000000000000), R := ((1107370706004464286067 : Rat) / 400000000000000000000), D0 := ((1107370706004464286067 : Rat) / 400000000000000000000), D1 := ((380380666004464286067 : Rat) / 400000000000000000000), D2 := ((84196706004464286067 : Rat) / 400000000000000000000), D3 := ((18988355290178572587 : Rat) / 400000000000000000000), D4 := ((20636140924107013733 : Rat) / 1280000000000000000000), LB := ((6151273419721659 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1107370706004464286067 : Rat) / 400000000000000000000), R := ((17718303616763392862809 : Rat) / 6400000000000000000000), D0 := ((17718303616763392862809 : Rat) / 6400000000000000000000), D1 := ((6086462976763392862809 : Rat) / 6400000000000000000000), D2 := ((1347519616763392862809 : Rat) / 6400000000000000000000), D3 := ((304186005334821447129 : Rat) / 6400000000000000000000), D4 := ((6425523995535673933 : Rat) / 400000000000000000000), LB := ((11783683315649829 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17718303616763392862809 : Rat) / 6400000000000000000000), R := ((8859337968727678574273 : Rat) / 3200000000000000000000), D0 := ((8859337968727678574273 : Rat) / 3200000000000000000000), D1 := ((3043417648727678574273 : Rat) / 3200000000000000000000), D2 := ((673945968727678574273 : Rat) / 3200000000000000000000), D3 := ((152279163013392866433 : Rat) / 3200000000000000000000), D4 := ((102436063236606497191 : Rat) / 6400000000000000000000), LB := ((11339693118508909 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8859337968727678574273 : Rat) / 3200000000000000000000), R := ((17719048258147321434283 : Rat) / 6400000000000000000000), D0 := ((17719048258147321434283 : Rat) / 6400000000000000000000), D1 := ((6087207618147321434283 : Rat) / 6400000000000000000000), D2 := ((1348264258147321434283 : Rat) / 6400000000000000000000), D3 := ((304930646718750018603 : Rat) / 6400000000000000000000), D4 := ((51031871272321105727 : Rat) / 3200000000000000000000), LB := ((4388394881535973 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17719048258147321434283 : Rat) / 6400000000000000000000), R := ((885971028941964286001 : Rat) / 320000000000000000000), D0 := ((885971028941964286001 : Rat) / 320000000000000000000), D1 := ((304378996941964286001 : Rat) / 320000000000000000000), D2 := ((67431828941964286001 : Rat) / 320000000000000000000), D3 := ((15265148370535715217 : Rat) / 320000000000000000000), D4 := ((101691421852677925717 : Rat) / 6400000000000000000000), LB := ((10677981463791397 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((885971028941964286001 : Rat) / 320000000000000000000), R := ((17719792899531250005757 : Rat) / 6400000000000000000000), D0 := ((17719792899531250005757 : Rat) / 6400000000000000000000), D1 := ((6087952259531250005757 : Rat) / 6400000000000000000000), D2 := ((1349008899531250005757 : Rat) / 6400000000000000000000), D3 := ((305675288102678590077 : Rat) / 6400000000000000000000), D4 := ((5065955058035681999 : Rat) / 320000000000000000000), LB := ((10461096794661673 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17719792899531250005757 : Rat) / 6400000000000000000000), R := ((8860082610111607145747 : Rat) / 3200000000000000000000), D0 := ((8860082610111607145747 : Rat) / 3200000000000000000000), D1 := ((3044162290111607145747 : Rat) / 3200000000000000000000), D2 := ((674690610111607145747 : Rat) / 3200000000000000000000), D3 := ((153023804397321437907 : Rat) / 3200000000000000000000), D4 := ((100946780468749354243 : Rat) / 6400000000000000000000), LB := ((2580189791748233 : Rat) / 12500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8860082610111607145747 : Rat) / 3200000000000000000000), R := ((17720537540915178577231 : Rat) / 6400000000000000000000), D0 := ((17720537540915178577231 : Rat) / 6400000000000000000000), D1 := ((6088696900915178577231 : Rat) / 6400000000000000000000), D2 := ((1349753540915178577231 : Rat) / 6400000000000000000000), D3 := ((306419929486607161551 : Rat) / 6400000000000000000000), D4 := ((50287229888392534253 : Rat) / 3200000000000000000000), LB := ((512869984795189 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17720537540915178577231 : Rat) / 6400000000000000000000), R := ((2215113732700892857871 : Rat) / 800000000000000000000), D0 := ((2215113732700892857871 : Rat) / 800000000000000000000), D1 := ((761133652700892857871 : Rat) / 800000000000000000000), D2 := ((168765732700892857871 : Rat) / 800000000000000000000), D3 := ((38349031272321430911 : Rat) / 800000000000000000000), D4 := ((100202139084820782769 : Rat) / 6400000000000000000000), LB := ((20542909426579659 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2215113732700892857871 : Rat) / 800000000000000000000), R := ((3544256436459821429741 : Rat) / 1280000000000000000000), D0 := ((3544256436459821429741 : Rat) / 1280000000000000000000), D1 := ((1217888308459821429741 : Rat) / 1280000000000000000000), D2 := ((270099636459821429741 : Rat) / 1280000000000000000000), D3 := ((12286582834821429321 : Rat) / 256000000000000000000), D4 := ((12478727299107062129 : Rat) / 800000000000000000000), LB := ((10363365841459249 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3544256436459821429741 : Rat) / 1280000000000000000000), R := ((8860827251495535717221 : Rat) / 3200000000000000000000), D0 := ((8860827251495535717221 : Rat) / 3200000000000000000000), D1 := ((3044906931495535717221 : Rat) / 3200000000000000000000), D2 := ((675435251495535717221 : Rat) / 3200000000000000000000), D3 := ((153768445781250009381 : Rat) / 3200000000000000000000), D4 := ((19891499540178442259 : Rat) / 1280000000000000000000), LB := ((2106716013443033 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8860827251495535717221 : Rat) / 3200000000000000000000), R := ((17722026823683035720179 : Rat) / 6400000000000000000000), D0 := ((17722026823683035720179 : Rat) / 6400000000000000000000), D1 := ((6090186183683035720179 : Rat) / 6400000000000000000000), D2 := ((1351242823683035720179 : Rat) / 6400000000000000000000), D3 := ((307909212254464304499 : Rat) / 6400000000000000000000), D4 := ((49542588504463962779 : Rat) / 3200000000000000000000), LB := ((539127490907787 : Rat) / 2500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17722026823683035720179 : Rat) / 6400000000000000000000), R := ((4430599786093750001479 : Rat) / 1600000000000000000000), D0 := ((4430599786093750001479 : Rat) / 1600000000000000000000), D1 := ((1522639626093750001479 : Rat) / 1600000000000000000000), D2 := ((337903786093750001479 : Rat) / 1600000000000000000000), D3 := ((77070383236607147559 : Rat) / 1600000000000000000000), D4 := ((98712856316963639821 : Rat) / 6400000000000000000000), LB := ((5555366519995053 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4430599786093750001479 : Rat) / 1600000000000000000000), R := ((17722771465066964291653 : Rat) / 6400000000000000000000), D0 := ((17722771465066964291653 : Rat) / 6400000000000000000000), D1 := ((6090930825066964291653 : Rat) / 6400000000000000000000), D2 := ((1351987465066964291653 : Rat) / 6400000000000000000000), D3 := ((308653853638392875973 : Rat) / 6400000000000000000000), D4 := ((24585133906249838521 : Rat) / 1600000000000000000000), LB := ((11518593275164357 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17722771465066964291653 : Rat) / 6400000000000000000000), R := ((1772314378575892857739 : Rat) / 640000000000000000000), D0 := ((1772314378575892857739 : Rat) / 640000000000000000000), D1 := ((609130314575892857739 : Rat) / 640000000000000000000), D2 := ((135235978575892857739 : Rat) / 640000000000000000000), D3 := ((30902617433035716171 : Rat) / 640000000000000000000), D4 := ((97968214933035068347 : Rat) / 6400000000000000000000), LB := ((3001649935805567 : Rat) / 12500000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1772314378575892857739 : Rat) / 640000000000000000000), R := ((17723516106450892863127 : Rat) / 6400000000000000000000), D0 := ((17723516106450892863127 : Rat) / 6400000000000000000000), D1 := ((6091675466450892863127 : Rat) / 6400000000000000000000), D2 := ((1352732106450892863127 : Rat) / 6400000000000000000000), D3 := ((309398495022321447447 : Rat) / 6400000000000000000000), D4 := ((9759589424107078261 : Rat) / 640000000000000000000), LB := ((2515045484435263 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17723516106450892863127 : Rat) / 6400000000000000000000), R := ((276935756674107142951 : Rat) / 100000000000000000000), D0 := ((276935756674107142951 : Rat) / 100000000000000000000), D1 := ((95188246674107142951 : Rat) / 100000000000000000000), D2 := ((21142256674107142951 : Rat) / 100000000000000000000), D3 := ((4840168995535714581 : Rat) / 100000000000000000000), D4 := ((97223573549106496873 : Rat) / 6400000000000000000000), LB := ((5289982852662023 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((276935756674107142951 : Rat) / 100000000000000000000), R := ((17724260747834821434601 : Rat) / 6400000000000000000000), D0 := ((17724260747834821434601 : Rat) / 6400000000000000000000), D1 := ((6092420107834821434601 : Rat) / 6400000000000000000000), D2 := ((1353476747834821434601 : Rat) / 6400000000000000000000), D3 := ((310143136406250018921 : Rat) / 6400000000000000000000), D4 := ((1513300825892847049 : Rat) / 100000000000000000000), LB := ((27912551235487193 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17724260747834821434601 : Rat) / 6400000000000000000000), R := ((8862316534263392860169 : Rat) / 3200000000000000000000), D0 := ((8862316534263392860169 : Rat) / 3200000000000000000000), D1 := ((3046396214263392860169 : Rat) / 3200000000000000000000), D2 := ((676924534263392860169 : Rat) / 3200000000000000000000), D3 := ((155257728549107152329 : Rat) / 3200000000000000000000), D4 := ((96478932165177925399 : Rat) / 6400000000000000000000), LB := ((2953935127730789 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8862316534263392860169 : Rat) / 3200000000000000000000), R := ((709000215568750000243 : Rat) / 256000000000000000000), D0 := ((709000215568750000243 : Rat) / 256000000000000000000), D1 := ((243726589968750000243 : Rat) / 256000000000000000000), D2 := ((54168855568750000243 : Rat) / 256000000000000000000), D3 := ((62177555558035718079 : Rat) / 1280000000000000000000), D4 := ((48053305736606819831 : Rat) / 3200000000000000000000), LB := ((7832828026478611 : Rat) / 25000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((709000215568750000243 : Rat) / 256000000000000000000), R := ((4431344427477678572953 : Rat) / 1600000000000000000000), D0 := ((4431344427477678572953 : Rat) / 1600000000000000000000), D1 := ((1523384267477678572953 : Rat) / 1600000000000000000000), D2 := ((338648427477678572953 : Rat) / 1600000000000000000000), D3 := ((77815024620535719033 : Rat) / 1600000000000000000000), D4 := ((3829371631249974157 : Rat) / 256000000000000000000), LB := ((3328944381726373 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4431344427477678572953 : Rat) / 1600000000000000000000), R := ((8863061175647321431643 : Rat) / 3200000000000000000000), D0 := ((8863061175647321431643 : Rat) / 3200000000000000000000), D1 := ((3047140855647321431643 : Rat) / 3200000000000000000000), D2 := ((677669175647321431643 : Rat) / 3200000000000000000000), D3 := ((156002369933035723803 : Rat) / 3200000000000000000000), D4 := ((23840492522321267047 : Rat) / 1600000000000000000000), LB := ((12268157270234337 : Rat) / 1000000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8863061175647321431643 : Rat) / 3200000000000000000000), R := ((443171674816964285869 : Rat) / 160000000000000000000), D0 := ((443171674816964285869 : Rat) / 160000000000000000000), D1 := ((152375658816964285869 : Rat) / 160000000000000000000), D2 := ((33902074816964285869 : Rat) / 160000000000000000000), D3 := ((7818734531250000477 : Rat) / 160000000000000000000), D4 := ((47308664352678248357 : Rat) / 3200000000000000000000), LB := ((60354944159901613 : Rat) / 1000000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((443171674816964285869 : Rat) / 160000000000000000000), R := ((8863805817031250003117 : Rat) / 3200000000000000000000), D0 := ((8863805817031250003117 : Rat) / 3200000000000000000000), D1 := ((3047885497031250003117 : Rat) / 3200000000000000000000), D2 := ((678413817031250003117 : Rat) / 3200000000000000000000), D3 := ((156747011316964295277 : Rat) / 3200000000000000000000), D4 := ((2346817183035698131 : Rat) / 160000000000000000000), LB := ((2305059831803069 : Rat) / 20000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8863805817031250003117 : Rat) / 3200000000000000000000), R := ((4432089068861607144427 : Rat) / 1600000000000000000000), D0 := ((4432089068861607144427 : Rat) / 1600000000000000000000), D1 := ((1524128908861607144427 : Rat) / 1600000000000000000000), D2 := ((339393068861607144427 : Rat) / 1600000000000000000000), D3 := ((78559666004464290507 : Rat) / 1600000000000000000000), D4 := ((46564022968749676883 : Rat) / 3200000000000000000000), LB := ((8852442236512159 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4432089068861607144427 : Rat) / 1600000000000000000000), R := ((8864550458415178574591 : Rat) / 3200000000000000000000), D0 := ((8864550458415178574591 : Rat) / 3200000000000000000000), D1 := ((3048630138415178574591 : Rat) / 3200000000000000000000), D2 := ((679158458415178574591 : Rat) / 3200000000000000000000), D3 := ((157491652700892866751 : Rat) / 3200000000000000000000), D4 := ((23095851138392695573 : Rat) / 1600000000000000000000), LB := ((2458312449798439 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8864550458415178574591 : Rat) / 3200000000000000000000), R := ((1108115347388392857541 : Rat) / 400000000000000000000), D0 := ((1108115347388392857541 : Rat) / 400000000000000000000), D1 := ((381125307388392857541 : Rat) / 400000000000000000000), D2 := ((84941347388392857541 : Rat) / 400000000000000000000), D3 := ((19732996674107144061 : Rat) / 400000000000000000000), D4 := ((45819381584821105409 : Rat) / 3200000000000000000000), LB := ((125660623763609 : Rat) / 390625000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1108115347388392857541 : Rat) / 400000000000000000000), R := ((1773059019959821429213 : Rat) / 640000000000000000000), D0 := ((1773059019959821429213 : Rat) / 640000000000000000000), D1 := ((609874955959821429213 : Rat) / 640000000000000000000), D2 := ((135980619959821429213 : Rat) / 640000000000000000000), D3 := ((6329451763392857529 : Rat) / 128000000000000000000), D4 := ((5680882611607102459 : Rat) / 400000000000000000000), LB := ((20236101865256373 : Rat) / 50000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1773059019959821429213 : Rat) / 640000000000000000000), R := ((4432833710245535715901 : Rat) / 1600000000000000000000), D0 := ((4432833710245535715901 : Rat) / 1600000000000000000000), D1 := ((1524873550245535715901 : Rat) / 1600000000000000000000), D2 := ((340137710245535715901 : Rat) / 1600000000000000000000), D3 := ((79304307388392861981 : Rat) / 1600000000000000000000), D4 := ((9014948040178506787 : Rat) / 640000000000000000000), LB := ((2475097539831883 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4432833710245535715901 : Rat) / 1600000000000000000000), R := ((8866039741183035717539 : Rat) / 3200000000000000000000), D0 := ((8866039741183035717539 : Rat) / 3200000000000000000000), D1 := ((3050119421183035717539 : Rat) / 3200000000000000000000), D2 := ((680647741183035717539 : Rat) / 3200000000000000000000), D3 := ((158980935468750009699 : Rat) / 3200000000000000000000), D4 := ((22351209754464124099 : Rat) / 1600000000000000000000), LB := ((370426143623849 : Rat) / 625000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8866039741183035717539 : Rat) / 3200000000000000000000), R := ((2216603015468750000819 : Rat) / 800000000000000000000), D0 := ((2216603015468750000819 : Rat) / 800000000000000000000), D1 := ((762622935468750000819 : Rat) / 800000000000000000000), D2 := ((170255015468750000819 : Rat) / 800000000000000000000), D3 := ((39838314040178573859 : Rat) / 800000000000000000000), D4 := ((44330098816963962461 : Rat) / 3200000000000000000000), LB := ((3489048904471437 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2216603015468750000819 : Rat) / 800000000000000000000), R := ((35468626813035714299 : Rat) / 12800000000000000000), D0 := ((35468626813035714299 : Rat) / 12800000000000000000), D1 := ((12204945533035714299 : Rat) / 12800000000000000000), D2 := ((2727058813035714299 : Rat) / 12800000000000000000), D3 := ((16009789754464286691 : Rat) / 320000000000000000000), D4 := ((10989444531249919181 : Rat) / 800000000000000000000), LB := ((107610801658789 : Rat) / 781250000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35468626813035714299 : Rat) / 12800000000000000000), R := ((554243834040178571639 : Rat) / 200000000000000000000), D0 := ((554243834040178571639 : Rat) / 200000000000000000000), D1 := ((190748814040178571639 : Rat) / 200000000000000000000), D2 := ((42656834040178571639 : Rat) / 200000000000000000000), D3 := ((10052658683035714899 : Rat) / 200000000000000000000), D4 := ((172852546964284421 : Rat) / 12800000000000000000), LB := ((3882568877859871 : Rat) / 10000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554243834040178571639 : Rat) / 200000000000000000000), R := ((4434322993013392858849 : Rat) / 1600000000000000000000), D0 := ((4434322993013392858849 : Rat) / 1600000000000000000000), D1 := ((1526362833013392858849 : Rat) / 1600000000000000000000), D2 := ((341626993013392858849 : Rat) / 1600000000000000000000), D3 := ((80793590156250004929 : Rat) / 1600000000000000000000), D4 := ((2654280959821408361 : Rat) / 200000000000000000000), LB := ((6703410032012913 : Rat) / 10000000000000000000) }
]

def block189RightChunk001L : Rat := ((168598466303571428511 : Rat) / 64000000000000000000)
def block189RightChunk001R : Rat := ((4434322993013392858849 : Rat) / 1600000000000000000000)

def block189RightChunk001Certificate : Bool :=
  allBoxesValid block189RightChunk001 &&
  coversFromBool block189RightChunk001 block189RightChunk001L block189RightChunk001R

theorem block189RightChunk001Certificate_eq_true :
    block189RightChunk001Certificate = true := by
  native_decide

def block189RightChunk002 : List RatBox := [
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4434322993013392858849 : Rat) / 1600000000000000000000), R := ((2217347656852678572293 : Rat) / 800000000000000000000), D0 := ((2217347656852678572293 : Rat) / 800000000000000000000), D1 := ((763367576852678572293 : Rat) / 800000000000000000000), D2 := ((170999656852678572293 : Rat) / 800000000000000000000), D3 := ((40582955424107145333 : Rat) / 800000000000000000000), D4 := ((20861926986606981151 : Rat) / 1600000000000000000000), LB := ((1969851404229117 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2217347656852678572293 : Rat) / 800000000000000000000), R := ((221771997754464285803 : Rat) / 80000000000000000000), D0 := ((221771997754464285803 : Rat) / 80000000000000000000), D1 := ((76373989754464285803 : Rat) / 80000000000000000000), D2 := ((17137197754464285803 : Rat) / 80000000000000000000), D3 := ((4095527611607143107 : Rat) / 80000000000000000000), D4 := ((10244803147321347707 : Rat) / 800000000000000000000), LB := ((3010648813056571 : Rat) / 500000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221771997754464285803 : Rat) / 80000000000000000000), R := ((2218092298236607143767 : Rat) / 800000000000000000000), D0 := ((2218092298236607143767 : Rat) / 800000000000000000000), D1 := ((764112218236607143767 : Rat) / 800000000000000000000), D2 := ((171744298236607143767 : Rat) / 800000000000000000000), D3 := ((41327596808035716807 : Rat) / 800000000000000000000), D4 := ((987248245535706197 : Rat) / 80000000000000000000), LB := ((4071983400609769 : Rat) / 5000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2218092298236607143767 : Rat) / 800000000000000000000), R := ((17331754835379464293 : Rat) / 6250000000000000000), D0 := ((17331754835379464293 : Rat) / 6250000000000000000), D1 := ((5972535460379464293 : Rat) / 6250000000000000000), D2 := ((1344661085379464293 : Rat) / 6250000000000000000), D3 := ((2606244843750000159 : Rat) / 50000000000000000000), D4 := ((9500161763392776233 : Rat) / 800000000000000000000), LB := ((442450768307151 : Rat) / 250000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17331754835379464293 : Rat) / 6250000000000000000), R := ((1109604630156250000489 : Rat) / 400000000000000000000), D0 := ((1109604630156250000489 : Rat) / 400000000000000000000), D1 := ((382614590156250000489 : Rat) / 400000000000000000000), D2 := ((86430630156250000489 : Rat) / 400000000000000000000), D3 := ((21222279441964287009 : Rat) / 400000000000000000000), D4 := ((35655629185267541 : Rat) / 3125000000000000000), LB := ((28391546553668823 : Rat) / 100000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109604630156250000489 : Rat) / 400000000000000000000), R := ((554988475424107143113 : Rat) / 200000000000000000000), D0 := ((554988475424107143113 : Rat) / 200000000000000000000), D1 := ((191493455424107143113 : Rat) / 200000000000000000000), D2 := ((43401475424107143113 : Rat) / 200000000000000000000), D3 := ((10797300066964286373 : Rat) / 200000000000000000000), D4 := ((4191599843749959511 : Rat) / 400000000000000000000), LB := ((6110602073612137 : Rat) / 2000000000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554988475424107143113 : Rat) / 200000000000000000000), R := ((11107215922321428577 : Rat) / 4000000000000000000), D0 := ((11107215922321428577 : Rat) / 4000000000000000000), D1 := ((3837315522321428577 : Rat) / 4000000000000000000), D2 := ((875475922321428577 : Rat) / 4000000000000000000), D3 := ((1116962075892857211 : Rat) / 20000000000000000000), D4 := ((1909639575892836887 : Rat) / 200000000000000000000), LB := ((3909501751687 : Rat) / 2500000000000000) },
  { w1 := ((1755381605390141 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((8945740556431009 : Rat) / 50000000000000000), w4 := ((9326946830381519 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((11107215922321428577 : Rat) / 4000000000000000000), R := ((139026359375000000081 : Rat) / 50000000000000000000), D0 := ((139026359375000000081 : Rat) / 50000000000000000000), D1 := ((48152604375000000081 : Rat) / 50000000000000000000), D2 := ((11129609375000000081 : Rat) / 50000000000000000000), D3 := ((372320691964285737 : Rat) / 6250000000000000000), D4 := ((30746377678571023 : Rat) / 4000000000000000000), LB := ((9909058189562503 : Rat) / 5000000000000000000) }
]

def block189RightChunk002L : Rat := ((4434322993013392858849 : Rat) / 1600000000000000000000)
def block189RightChunk002R : Rat := ((139026359375000000081 : Rat) / 50000000000000000000)

def block189RightChunk002Certificate : Bool :=
  allBoxesValid block189RightChunk002 &&
  coversFromBool block189RightChunk002 block189RightChunk002L block189RightChunk002R

theorem block189RightChunk002Certificate_eq_true :
    block189RightChunk002Certificate = true := by
  native_decide

def block189RightChainCertificate : Bool :=
  decide (
    block189RightL = ((8901658482142857151 : Rat) / 5000000000000000000) /\
    ((168598466303571428511 : Rat) / 64000000000000000000) = ((168598466303571428511 : Rat) / 64000000000000000000) /\
    ((4434322993013392858849 : Rat) / 1600000000000000000000) = ((4434322993013392858849 : Rat) / 1600000000000000000000) /\
    ((139026359375000000081 : Rat) / 50000000000000000000) = block189RightR)

theorem block189RightChainCertificate_eq_true :
    block189RightChainCertificate = true := by
  native_decide

def block189LeftBoxCount : Nat := boxCount block189LeftBoxes
def block189RightBoxCount : Nat := 208

def block189_rational_certificate : Prop :=
    block189LeftCertificate = true /\
    block189RightChainCertificate = true /\
    block189RightChunk000Certificate = true /\
    block189RightChunk001Certificate = true /\
    block189RightChunk002Certificate = true

theorem block189_rational_certificate_proof :
    block189_rational_certificate := by
  exact ⟨block189LeftCertificate_eq_true, block189RightChainCertificate_eq_true, block189RightChunk000Certificate_eq_true, block189RightChunk001Certificate_eq_true, block189RightChunk002Certificate_eq_true⟩

end Block189
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block189

open Set

def block189W1 : Rat := ((1755381605390141 : Rat) / 1000000000000000)
def block189W2 : Rat := (0 : Rat)
def block189W3 : Rat := ((8945740556431009 : Rat) / 50000000000000000)
def block189W4 : Rat := ((9326946830381519 : Rat) / 100000000000000000)
def block189S1 : Rat := ((18174751 : Rat) / 10000000)
def block189S2 : Rat := ((511587 : Rat) / 200000)
def block189S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block189S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block189V (y : ℝ) : ℝ :=
  ratPotential block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4 y

def block189LeftParamsCertificate : Bool :=
  allBoxesSameParams block189LeftBoxes block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189LeftParamsCertificate_eq_true :
    block189LeftParamsCertificate = true := by
  native_decide

theorem block189_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189LeftL : ℝ) (block189LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189LeftCertificate_eq_true
  unfold block189LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189LeftBoxes) (lo := block189LeftL) (hi := block189LeftR)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block189RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block189RightChunk000 block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189RightChunk000ParamsCertificate_eq_true :
    block189RightChunk000ParamsCertificate = true := by
  native_decide

theorem block189_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightChunk000L : ℝ) (block189RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189RightChunk000Certificate_eq_true
  unfold block189RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189RightChunk000) (lo := block189RightChunk000L) (hi := block189RightChunk000R)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block189RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block189RightChunk001 block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189RightChunk001ParamsCertificate_eq_true :
    block189RightChunk001ParamsCertificate = true := by
  native_decide

theorem block189_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightChunk001L : ℝ) (block189RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189RightChunk001Certificate_eq_true
  unfold block189RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189RightChunk001) (lo := block189RightChunk001L) (hi := block189RightChunk001R)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block189RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block189RightChunk002 block189W1 block189W2 block189W3 block189W4 block189S1 block189S2 block189S3 block189S4

theorem block189RightChunk002ParamsCertificate_eq_true :
    block189RightChunk002ParamsCertificate = true := by
  native_decide

theorem block189_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightChunk002L : ℝ) (block189RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  have hcert := block189RightChunk002Certificate_eq_true
  unfold block189RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block189RightChunk002) (lo := block189RightChunk002L) (hi := block189RightChunk002R)
    (w1 := block189W1) (w2 := block189W2) (w3 := block189W3) (w4 := block189W4)
    (s1 := block189S1) (s2 := block189S2) (s3 := block189S3) (s4 := block189S4)
    hboxes hcover block189RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block189_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block189RightL : ℝ) (block189RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block189S1 : ℝ))
    (hy2ne : y ≠ (block189S2 : ℝ))
    (hy3ne : y ≠ (block189S3 : ℝ))
    (hy4ne : y ≠ (block189S4 : ℝ)) :
    0 < block189V y := by
  by_cases h0 : y ≤ (block189RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block189RightChunk000L : ℝ) (block189RightChunk000R : ℝ) := by
      have hL : (block189RightChunk000L : ℝ) = (block189RightL : ℝ) := by
        norm_num [block189RightChunk000L, block189RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block189_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block189RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block189RightChunk001L : ℝ) (block189RightChunk001R : ℝ) := by
        have hprev : (block189RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block189RightChunk001L : ℝ) = (block189RightChunk000R : ℝ) := by
          norm_num [block189RightChunk001L, block189RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block189_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block189RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block189RightChunk002L : ℝ) = (block189RightChunk001R : ℝ) := by
        norm_num [block189RightChunk002L, block189RightChunk001R]
      have hR : (block189RightChunk002R : ℝ) = (block189RightR : ℝ) := by
        norm_num [block189RightChunk002R, block189RightR]
      have hyc : y ∈ Icc (block189RightChunk002L : ℝ) (block189RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block189_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block189_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block189LeftL : ℝ) (block189LeftR : ℝ) →
    y ≠ 0 → y ≠ (block189S1 : ℝ) → y ≠ (block189S2 : ℝ) →
    y ≠ (block189S3 : ℝ) → y ≠ (block189S4 : ℝ) → 0 < block189V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block189RightL : ℝ) (block189RightR : ℝ) →
    y ≠ 0 → y ≠ (block189S1 : ℝ) → y ≠ (block189S2 : ℝ) →
    y ≠ (block189S3 : ℝ) → y ≠ (block189S4 : ℝ) → 0 < block189V y)

theorem block189_reallog_certificate_proof :
    block189_reallog_certificate := by
  exact ⟨block189_left_V_pos, block189_right_V_pos⟩

end Block189
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block189.block189V
#check Erdos1038Lean.M1817475.Block189.block189_left_V_pos
#check Erdos1038Lean.M1817475.Block189.block189_right_V_pos
#check Erdos1038Lean.M1817475.Block189.block189_reallog_certificate_proof
