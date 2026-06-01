/-
Self-contained Lean4Web paste file.
Block 111 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block111

def block111LeftL : Rat := ((2486187500000000003 : Rat) / 3125000000000000000)
def block111LeftR : Rat := ((39788774553571428619 : Rat) / 50000000000000000000)
def block111RightL : Rat := ((5611187500000000003 : Rat) / 3125000000000000000)
def block111RightR : Rat := ((139788774553571428619 : Rat) / 50000000000000000000)

def block111LeftBoxes : List RatBox := [
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2486187500000000003 : Rat) / 3125000000000000000), R := ((39788774553571428619 : Rat) / 50000000000000000000), D0 := ((39788774553571428619 : Rat) / 50000000000000000000), D1 := ((3193422187499999997 : Rat) / 3125000000000000000), D2 := ((5507359374999999997 : Rat) / 3125000000000000000), D3 := ((96268793839285714137 : Rat) / 50000000000000000000), D4 := ((12430691093749999369 : Rat) / 6250000000000000000), LB := ((6424170180483121 : Rat) / 1000000000000000000) }
]

def block111LeftCertificate : Bool :=
  allBoxesValid block111LeftBoxes &&
  coversFromBool block111LeftBoxes block111LeftL block111LeftR

theorem block111LeftCertificate_eq_true :
    block111LeftCertificate = true := by
  native_decide

def block111RightChunk000 : List RatBox := [
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5611187500000000003 : Rat) / 3125000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((68422187499999997 : Rat) / 3125000000000000000), D2 := ((2382359374999999997 : Rat) / 3125000000000000000), D3 := ((46268793839285714137 : Rat) / 50000000000000000000), D4 := ((6180691093749999369 : Rat) / 6250000000000000000), LB := ((9025651535914637 : Rat) / 1000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((8651154541585231 : Rat) / 5000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((187716446044029 : Rat) / 250000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((4720737208122501 : Rat) / 100000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((274164030898979 : Rat) / 5000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((18589769173748827 : Rat) / 500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((6926397442734411 : Rat) / 200000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((1787714777305871 : Rat) / 100000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((1567091413842453 : Rat) / 500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((988940085455553 : Rat) / 125000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((13134858222869361 : Rat) / 5000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((1703916959482142856317 : Rat) / 640000000000000000000), D0 := ((1703916959482142856317 : Rat) / 640000000000000000000), D1 := ((540732895482142856317 : Rat) / 640000000000000000000), D2 := ((66838559482142856317 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((6644992505582481 : Rat) / 1000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1703916959482142856317 : Rat) / 640000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((37494801660714285251 : Rat) / 640000000000000000000), D4 := ((78157008517857079683 : Rat) / 640000000000000000000), LB := ((936406474572049 : Rat) / 200000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((1707177377017857141991 : Rat) / 640000000000000000000), D0 := ((1707177377017857141991 : Rat) / 640000000000000000000), D1 := ((543993313017857141991 : Rat) / 640000000000000000000), D2 := ((70098977017857141991 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((368506350336327 : Rat) / 125000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1707177377017857141991 : Rat) / 640000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((34234384124999999577 : Rat) / 640000000000000000000), D4 := ((74896590982142794009 : Rat) / 640000000000000000000), LB := ((3645282322279203 : Rat) / 2500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((342087558910714285533 : Rat) / 128000000000000000000), D0 := ((342087558910714285533 : Rat) / 128000000000000000000), D1 := ((109450746110714285533 : Rat) / 128000000000000000000), D2 := ((14671878910714285533 : Rat) / 128000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((4584817995776369 : Rat) / 20000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((342087558910714285533 : Rat) / 128000000000000000000), R := ((3422505797874999998167 : Rat) / 1280000000000000000000), D0 := ((3422505797874999998167 : Rat) / 1280000000000000000000), D1 := ((1096137669874999998167 : Rat) / 1280000000000000000000), D2 := ((148348997874999998167 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 640000000000000000000), D4 := ((14327234689285701667 : Rat) / 128000000000000000000), LB := ((6992960109268087 : Rat) / 2000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3422505797874999998167 : Rat) / 1280000000000000000000), R := ((856034001660714285251 : Rat) / 320000000000000000000), D0 := ((856034001660714285251 : Rat) / 320000000000000000000), D1 := ((274441969660714285251 : Rat) / 320000000000000000000), D2 := ((37494801660714285251 : Rat) / 320000000000000000000), D3 := ((60317724410714284969 : Rat) / 1280000000000000000000), D4 := ((141642138124999873833 : Rat) / 1280000000000000000000), LB := ((97763664924767 : Rat) / 31250000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((856034001660714285251 : Rat) / 320000000000000000000), R := ((3425766215410714283841 : Rat) / 1280000000000000000000), D0 := ((3425766215410714283841 : Rat) / 1280000000000000000000), D1 := ((1099398087410714283841 : Rat) / 1280000000000000000000), D2 := ((151609415410714283841 : Rat) / 1280000000000000000000), D3 := ((14671878910714285533 : Rat) / 320000000000000000000), D4 := ((35002982339285682749 : Rat) / 320000000000000000000), LB := ((354884717034501 : Rat) / 125000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3425766215410714283841 : Rat) / 1280000000000000000000), R := ((1713698212089285713339 : Rat) / 640000000000000000000), D0 := ((1713698212089285713339 : Rat) / 640000000000000000000), D1 := ((550514148089285713339 : Rat) / 640000000000000000000), D2 := ((76619812089285713339 : Rat) / 640000000000000000000), D3 := ((11411461374999999859 : Rat) / 256000000000000000000), D4 := ((138381720589285588159 : Rat) / 1280000000000000000000), LB := ((26317097363287023 : Rat) / 10000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1713698212089285713339 : Rat) / 640000000000000000000), R := ((685805326589285713903 : Rat) / 256000000000000000000), D0 := ((685805326589285713903 : Rat) / 256000000000000000000), D1 := ((220531700989285713903 : Rat) / 256000000000000000000), D2 := ((30973966589285713903 : Rat) / 256000000000000000000), D3 := ((27713549053571428229 : Rat) / 640000000000000000000), D4 := ((68375755910714222661 : Rat) / 640000000000000000000), LB := ((1254951101818863 : Rat) / 500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((685805326589285713903 : Rat) / 256000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((53796889339285713621 : Rat) / 1280000000000000000000), D4 := ((27024260610714260497 : Rat) / 256000000000000000000), LB := ((6193785972228999 : Rat) / 2500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((3432287050482142855189 : Rat) / 1280000000000000000000), D0 := ((3432287050482142855189 : Rat) / 1280000000000000000000), D1 := ((1105918922482142855189 : Rat) / 1280000000000000000000), D2 := ((158130250482142855189 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((2538730055565319 : Rat) / 1000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3432287050482142855189 : Rat) / 1280000000000000000000), R := ((1716958629624999999013 : Rat) / 640000000000000000000), D0 := ((1716958629624999999013 : Rat) / 640000000000000000000), D1 := ((553774565624999999013 : Rat) / 640000000000000000000), D2 := ((79880229624999999013 : Rat) / 640000000000000000000), D3 := ((50536471803571427947 : Rat) / 1280000000000000000000), D4 := ((131860885517857016811 : Rat) / 1280000000000000000000), LB := ((168631062438529 : Rat) / 62500000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1716958629624999999013 : Rat) / 640000000000000000000), R := ((3435547468017857140863 : Rat) / 1280000000000000000000), D0 := ((3435547468017857140863 : Rat) / 1280000000000000000000), D1 := ((1109179340017857140863 : Rat) / 1280000000000000000000), D2 := ((161390668017857140863 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 128000000000000000000), D4 := ((65115338374999936987 : Rat) / 640000000000000000000), LB := ((740143234618143 : Rat) / 250000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3435547468017857140863 : Rat) / 1280000000000000000000), R := ((34371776767857142837 : Rat) / 12800000000000000000), D0 := ((34371776767857142837 : Rat) / 12800000000000000000), D1 := ((11108095487857142837 : Rat) / 12800000000000000000), D2 := ((1630208767857142837 : Rat) / 12800000000000000000), D3 := ((47276054267857142273 : Rat) / 1280000000000000000000), D4 := ((128600467982142731137 : Rat) / 1280000000000000000000), LB := ((4164473837947047 : Rat) / 1250000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((34371776767857142837 : Rat) / 12800000000000000000), R := ((3438807885553571426537 : Rat) / 1280000000000000000000), D0 := ((3438807885553571426537 : Rat) / 1280000000000000000000), D1 := ((1112439757553571426537 : Rat) / 1280000000000000000000), D2 := ((164651085553571426537 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 320000000000000000000), D4 := ((1269702592142855883 : Rat) / 12800000000000000000), LB := ((19085314436517453 : Rat) / 5000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3438807885553571426537 : Rat) / 1280000000000000000000), R := ((1720219047160714284687 : Rat) / 640000000000000000000), D0 := ((1720219047160714284687 : Rat) / 640000000000000000000), D1 := ((557034983160714284687 : Rat) / 640000000000000000000), D2 := ((83140647160714284687 : Rat) / 640000000000000000000), D3 := ((44015636732142856599 : Rat) / 1280000000000000000000), D4 := ((125340050446428445463 : Rat) / 1280000000000000000000), LB := ((11058930687381091 : Rat) / 2500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1720219047160714284687 : Rat) / 640000000000000000000), R := ((430462313982142856881 : Rat) / 160000000000000000000), D0 := ((430462313982142856881 : Rat) / 160000000000000000000), D1 := ((139666297982142856881 : Rat) / 160000000000000000000), D2 := ((21192713982142856881 : Rat) / 160000000000000000000), D3 := ((21192713982142856881 : Rat) / 640000000000000000000), D4 := ((61854920839285651313 : Rat) / 640000000000000000000), LB := ((39487447829889 : Rat) / 39062500000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((430462313982142856881 : Rat) / 160000000000000000000), R := ((1723479464696428570361 : Rat) / 640000000000000000000), D0 := ((1723479464696428570361 : Rat) / 640000000000000000000), D1 := ((560295400696428570361 : Rat) / 640000000000000000000), D2 := ((86401064696428570361 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 160000000000000000000), D4 := ((15056178017857127119 : Rat) / 160000000000000000000), LB := ((5818778137662961 : Rat) / 2000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1723479464696428570361 : Rat) / 640000000000000000000), R := ((862554836732142856599 : Rat) / 320000000000000000000), D0 := ((862554836732142856599 : Rat) / 320000000000000000000), D1 := ((280962804732142856599 : Rat) / 320000000000000000000), D2 := ((44015636732142856599 : Rat) / 320000000000000000000), D3 := ((17932296446428571207 : Rat) / 640000000000000000000), D4 := ((58594503303571365639 : Rat) / 640000000000000000000), LB := ((543014158529137 : Rat) / 100000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((862554836732142856599 : Rat) / 320000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 64000000000000000000), D4 := ((28482147267857111401 : Rat) / 320000000000000000000), LB := ((11446459493531791 : Rat) / 25000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((865815254267857142273 : Rat) / 320000000000000000000), D0 := ((865815254267857142273 : Rat) / 320000000000000000000), D1 := ((284223222267857142273 : Rat) / 320000000000000000000), D2 := ((47276054267857142273 : Rat) / 320000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((1210352823428143 : Rat) / 125000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((865815254267857142273 : Rat) / 320000000000000000000), R := ((86744546303571428511 : Rat) / 32000000000000000000), D0 := ((86744546303571428511 : Rat) / 32000000000000000000), D1 := ((28585343103571428511 : Rat) / 32000000000000000000), D2 := ((4890626303571428511 : Rat) / 32000000000000000000), D3 := ((4890626303571428511 : Rat) / 320000000000000000000), D4 := ((25221729732142825727 : Rat) / 320000000000000000000), LB := ((299933717169943 : Rat) / 12500000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86744546303571428511 : Rat) / 32000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 160000000000000000000), D4 := ((2359152096428568289 : Rat) / 32000000000000000000), LB := ((120853153368771 : Rat) / 3906250000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((218311817124999998859 : Rat) / 80000000000000000000), D0 := ((218311817124999998859 : Rat) / 80000000000000000000), D1 := ((72913809124999998859 : Rat) / 80000000000000000000), D2 := ((13677017124999998859 : Rat) / 80000000000000000000), D3 := ((635346982142856163 : Rat) / 80000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((987572636773767 : Rat) / 20000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((218311817124999998859 : Rat) / 80000000000000000000), R := ((109473582053571427511 : Rat) / 40000000000000000000), D0 := ((109473582053571427511 : Rat) / 40000000000000000000), D1 := ((36774578053571427511 : Rat) / 40000000000000000000), D2 := ((7156182053571427511 : Rat) / 40000000000000000000), D3 := ((635346982142856163 : Rat) / 40000000000000000000), D4 := ((4447428874999993141 : Rat) / 80000000000000000000), LB := ((1065824186955111 : Rat) / 500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((109473582053571427511 : Rat) / 40000000000000000000), R := ((438529675196428566207 : Rat) / 160000000000000000000), D0 := ((438529675196428566207 : Rat) / 160000000000000000000), D1 := ((147733659196428566207 : Rat) / 160000000000000000000), D2 := ((29260075196428566207 : Rat) / 160000000000000000000), D3 := ((635346982142856163 : Rat) / 32000000000000000000), D4 := ((1906040946428568489 : Rat) / 40000000000000000000), LB := ((12606163140839177 : Rat) / 5000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((438529675196428566207 : Rat) / 160000000000000000000), R := ((877694697374999988577 : Rat) / 320000000000000000000), D0 := ((877694697374999988577 : Rat) / 320000000000000000000), D1 := ((296102665374999988577 : Rat) / 320000000000000000000), D2 := ((59155497374999988577 : Rat) / 320000000000000000000), D3 := ((6988816803571417793 : Rat) / 320000000000000000000), D4 := ((6988816803571417793 : Rat) / 160000000000000000000), LB := ((11223009302721021 : Rat) / 2000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((877694697374999988577 : Rat) / 320000000000000000000), R := ((43916502217857142237 : Rat) / 16000000000000000000), D0 := ((43916502217857142237 : Rat) / 16000000000000000000), D1 := ((14836900617857142237 : Rat) / 16000000000000000000), D2 := ((2989542217857142237 : Rat) / 16000000000000000000), D3 := ((1906040946428568489 : Rat) / 80000000000000000000), D4 := ((13342286624999979423 : Rat) / 320000000000000000000), LB := ((40002162633197 : Rat) / 20000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43916502217857142237 : Rat) / 16000000000000000000), R := ((1757295435696428545643 : Rat) / 640000000000000000000), D0 := ((1757295435696428545643 : Rat) / 640000000000000000000), D1 := ((594111371696428545643 : Rat) / 640000000000000000000), D2 := ((120217035696428545643 : Rat) / 640000000000000000000), D3 := ((635346982142856163 : Rat) / 25600000000000000000), D4 := ((635346982142856163 : Rat) / 16000000000000000000), LB := ((2482058930272979 : Rat) / 500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1757295435696428545643 : Rat) / 640000000000000000000), R := ((878965391339285700903 : Rat) / 320000000000000000000), D0 := ((878965391339285700903 : Rat) / 320000000000000000000), D1 := ((297373359339285700903 : Rat) / 320000000000000000000), D2 := ((60426191339285700903 : Rat) / 320000000000000000000), D3 := ((8259510767857130119 : Rat) / 320000000000000000000), D4 := ((24778532303571390357 : Rat) / 640000000000000000000), LB := ((38235208530059683 : Rat) / 10000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((878965391339285700903 : Rat) / 320000000000000000000), R := ((1758566129660714257969 : Rat) / 640000000000000000000), D0 := ((1758566129660714257969 : Rat) / 640000000000000000000), D1 := ((595382065660714257969 : Rat) / 640000000000000000000), D2 := ((121487729660714257969 : Rat) / 640000000000000000000), D3 := ((17154368517857116401 : Rat) / 640000000000000000000), D4 := ((12071592660714267097 : Rat) / 320000000000000000000), LB := ((7258852674688343 : Rat) / 2500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1758566129660714257969 : Rat) / 640000000000000000000), R := ((439800369160714278533 : Rat) / 160000000000000000000), D0 := ((439800369160714278533 : Rat) / 160000000000000000000), D1 := ((149004353160714278533 : Rat) / 160000000000000000000), D2 := ((30530769160714278533 : Rat) / 160000000000000000000), D3 := ((4447428874999993141 : Rat) / 160000000000000000000), D4 := ((23507838339285678031 : Rat) / 640000000000000000000), LB := ((220323326394789 : Rat) / 100000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((439800369160714278533 : Rat) / 160000000000000000000), R := ((351967364724999994059 : Rat) / 128000000000000000000), D0 := ((351967364724999994059 : Rat) / 128000000000000000000), D1 := ((119330551924999994059 : Rat) / 128000000000000000000), D2 := ((24551684724999994059 : Rat) / 128000000000000000000), D3 := ((18425062482142828727 : Rat) / 640000000000000000000), D4 := ((5718122839285705467 : Rat) / 160000000000000000000), LB := ((344586491146881 : Rat) / 200000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((351967364724999994059 : Rat) / 128000000000000000000), R := ((880236085303571413229 : Rat) / 320000000000000000000), D0 := ((880236085303571413229 : Rat) / 320000000000000000000), D1 := ((298644053303571413229 : Rat) / 320000000000000000000), D2 := ((61696885303571413229 : Rat) / 320000000000000000000), D3 := ((1906040946428568489 : Rat) / 64000000000000000000), D4 := ((4447428874999993141 : Rat) / 128000000000000000000), LB := ((1464208919863097 : Rat) / 1000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((880236085303571413229 : Rat) / 320000000000000000000), R := ((1761107517589285682621 : Rat) / 640000000000000000000), D0 := ((1761107517589285682621 : Rat) / 640000000000000000000), D1 := ((597923453589285682621 : Rat) / 640000000000000000000), D2 := ((124029117589285682621 : Rat) / 640000000000000000000), D3 := ((19695756446428541053 : Rat) / 640000000000000000000), D4 := ((10800898696428554771 : Rat) / 320000000000000000000), LB := ((571939433802493 : Rat) / 400000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1761107517589285682621 : Rat) / 640000000000000000000), R := ((55054464517857141837 : Rat) / 20000000000000000000), D0 := ((55054464517857141837 : Rat) / 20000000000000000000), D1 := ((18704962517857141837 : Rat) / 20000000000000000000), D2 := ((3895764517857141837 : Rat) / 20000000000000000000), D3 := ((635346982142856163 : Rat) / 20000000000000000000), D4 := ((20966450410714253379 : Rat) / 640000000000000000000), LB := ((16238571343567543 : Rat) / 10000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55054464517857141837 : Rat) / 20000000000000000000), R := ((1762378211553571394947 : Rat) / 640000000000000000000), D0 := ((1762378211553571394947 : Rat) / 640000000000000000000), D1 := ((599194147553571394947 : Rat) / 640000000000000000000), D2 := ((125299811553571394947 : Rat) / 640000000000000000000), D3 := ((20966450410714253379 : Rat) / 640000000000000000000), D4 := ((635346982142856163 : Rat) / 20000000000000000000), LB := ((2051487127779139 : Rat) / 1000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1762378211553571394947 : Rat) / 640000000000000000000), R := ((176301355853571425111 : Rat) / 64000000000000000000), D0 := ((176301355853571425111 : Rat) / 64000000000000000000), D1 := ((59982949453571425111 : Rat) / 64000000000000000000), D2 := ((12593515853571425111 : Rat) / 64000000000000000000), D3 := ((10800898696428554771 : Rat) / 320000000000000000000), D4 := ((19695756446428541053 : Rat) / 640000000000000000000), LB := ((13596441885264099 : Rat) / 5000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((176301355853571425111 : Rat) / 64000000000000000000), R := ((1763648905517857107273 : Rat) / 640000000000000000000), D0 := ((1763648905517857107273 : Rat) / 640000000000000000000), D1 := ((600464841517857107273 : Rat) / 640000000000000000000), D2 := ((126570505517857107273 : Rat) / 640000000000000000000), D3 := ((4447428874999993141 : Rat) / 128000000000000000000), D4 := ((1906040946428568489 : Rat) / 64000000000000000000), LB := ((363518276400121 : Rat) / 100000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1763648905517857107273 : Rat) / 640000000000000000000), R := ((441071063124999990859 : Rat) / 160000000000000000000), D0 := ((441071063124999990859 : Rat) / 160000000000000000000), D1 := ((150275047124999990859 : Rat) / 160000000000000000000), D2 := ((31801463124999990859 : Rat) / 160000000000000000000), D3 := ((5718122839285705467 : Rat) / 160000000000000000000), D4 := ((18425062482142828727 : Rat) / 640000000000000000000), LB := ((240428281780547 : Rat) / 50000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441071063124999990859 : Rat) / 160000000000000000000), R := ((882777473232142837881 : Rat) / 320000000000000000000), D0 := ((882777473232142837881 : Rat) / 320000000000000000000), D1 := ((301185441232142837881 : Rat) / 320000000000000000000), D2 := ((64238273232142837881 : Rat) / 320000000000000000000), D3 := ((12071592660714267097 : Rat) / 320000000000000000000), D4 := ((4447428874999993141 : Rat) / 160000000000000000000), LB := ((1442538588394271 : Rat) / 1000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((882777473232142837881 : Rat) / 320000000000000000000), R := ((220853205053571423511 : Rat) / 80000000000000000000), D0 := ((220853205053571423511 : Rat) / 80000000000000000000), D1 := ((75455197053571423511 : Rat) / 80000000000000000000), D2 := ((16218405053571423511 : Rat) / 80000000000000000000), D3 := ((635346982142856163 : Rat) / 16000000000000000000), D4 := ((8259510767857130119 : Rat) / 320000000000000000000), LB := ((2640714043591119 : Rat) / 500000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220853205053571423511 : Rat) / 80000000000000000000), R := ((88468351417857140637 : Rat) / 32000000000000000000), D0 := ((88468351417857140637 : Rat) / 32000000000000000000), D1 := ((30309148217857140637 : Rat) / 32000000000000000000), D2 := ((6614431417857140637 : Rat) / 32000000000000000000), D3 := ((6988816803571417793 : Rat) / 160000000000000000000), D4 := ((1906040946428568489 : Rat) / 80000000000000000000), LB := ((12404696721881603 : Rat) / 10000000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((88468351417857140637 : Rat) / 32000000000000000000), R := ((110744276017857139837 : Rat) / 40000000000000000000), D0 := ((110744276017857139837 : Rat) / 40000000000000000000), D1 := ((38045272017857139837 : Rat) / 40000000000000000000), D2 := ((8426876017857139837 : Rat) / 40000000000000000000), D3 := ((1906040946428568489 : Rat) / 40000000000000000000), D4 := ((635346982142856163 : Rat) / 32000000000000000000), LB := ((3234227328347039 : Rat) / 200000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110744276017857139837 : Rat) / 40000000000000000000), R := ((222123899017857135837 : Rat) / 80000000000000000000), D0 := ((222123899017857135837 : Rat) / 80000000000000000000), D1 := ((76725891017857135837 : Rat) / 80000000000000000000), D2 := ((17489099017857135837 : Rat) / 80000000000000000000), D3 := ((4447428874999993141 : Rat) / 80000000000000000000), D4 := ((635346982142856163 : Rat) / 40000000000000000000), LB := ((5523406125619773 : Rat) / 250000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((222123899017857135837 : Rat) / 80000000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((635346982142856163 : Rat) / 10000000000000000000), D4 := ((635346982142856163 : Rat) / 80000000000000000000), LB := ((5685912482568217 : Rat) / 50000000000000000) },
  { w1 := ((12581320908151399 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((1680427322491631 : Rat) / 25000000000000000), w4 := ((56119845540779 : Rat) / 312500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((139788774553571428619 : Rat) / 50000000000000000000), D0 := ((139788774553571428619 : Rat) / 50000000000000000000), D1 := ((48915019553571428619 : Rat) / 50000000000000000000), D2 := ((11892024553571428619 : Rat) / 50000000000000000000), D3 := ((1870490357142857217 : Rat) / 25000000000000000000), D4 := ((564245803571433619 : Rat) / 50000000000000000000), LB := ((13286016297309633 : Rat) / 2000000000000000000) }
]

def block111RightChunk000L : Rat := ((5611187500000000003 : Rat) / 3125000000000000000)
def block111RightChunk000R : Rat := ((139788774553571428619 : Rat) / 50000000000000000000)

def block111RightChunk000Certificate : Bool :=
  allBoxesValid block111RightChunk000 &&
  coversFromBool block111RightChunk000 block111RightChunk000L block111RightChunk000R

theorem block111RightChunk000Certificate_eq_true :
    block111RightChunk000Certificate = true := by
  native_decide

def block111RightChainCertificate : Bool :=
  decide (
    block111RightL = ((5611187500000000003 : Rat) / 3125000000000000000) /\
    ((139788774553571428619 : Rat) / 50000000000000000000) = block111RightR)

theorem block111RightChainCertificate_eq_true :
    block111RightChainCertificate = true := by
  native_decide

def block111LeftBoxCount : Nat := boxCount block111LeftBoxes
def block111RightBoxCount : Nat := 59

def block111_rational_certificate : Prop :=
    block111LeftCertificate = true /\
    block111RightChainCertificate = true /\
    block111RightChunk000Certificate = true

theorem block111_rational_certificate_proof :
    block111_rational_certificate := by
  exact ⟨block111LeftCertificate_eq_true, block111RightChainCertificate_eq_true, block111RightChunk000Certificate_eq_true⟩

end Block111
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block111

open Set

def block111W1 : Rat := ((12581320908151399 : Rat) / 5000000000000000)
def block111W2 : Rat := (0 : Rat)
def block111W3 : Rat := ((1680427322491631 : Rat) / 25000000000000000)
def block111W4 : Rat := ((56119845540779 : Rat) / 312500000000000)
def block111S1 : Rat := ((18174751 : Rat) / 10000000)
def block111S2 : Rat := ((511587 : Rat) / 200000)
def block111S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block111S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block111V (y : ℝ) : ℝ :=
  ratPotential block111W1 block111W2 block111W3 block111W4 block111S1 block111S2 block111S3 block111S4 y

def block111LeftParamsCertificate : Bool :=
  allBoxesSameParams block111LeftBoxes block111W1 block111W2 block111W3 block111W4 block111S1 block111S2 block111S3 block111S4

theorem block111LeftParamsCertificate_eq_true :
    block111LeftParamsCertificate = true := by
  native_decide

theorem block111_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block111LeftL : ℝ) (block111LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block111S1 : ℝ))
    (hy2ne : y ≠ (block111S2 : ℝ))
    (hy3ne : y ≠ (block111S3 : ℝ))
    (hy4ne : y ≠ (block111S4 : ℝ)) :
    0 < block111V y := by
  have hcert := block111LeftCertificate_eq_true
  unfold block111LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block111LeftBoxes) (lo := block111LeftL) (hi := block111LeftR)
    (w1 := block111W1) (w2 := block111W2) (w3 := block111W3) (w4 := block111W4)
    (s1 := block111S1) (s2 := block111S2) (s3 := block111S3) (s4 := block111S4)
    hboxes hcover block111LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block111RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block111RightChunk000 block111W1 block111W2 block111W3 block111W4 block111S1 block111S2 block111S3 block111S4

theorem block111RightChunk000ParamsCertificate_eq_true :
    block111RightChunk000ParamsCertificate = true := by
  native_decide

theorem block111_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block111RightChunk000L : ℝ) (block111RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block111S1 : ℝ))
    (hy2ne : y ≠ (block111S2 : ℝ))
    (hy3ne : y ≠ (block111S3 : ℝ))
    (hy4ne : y ≠ (block111S4 : ℝ)) :
    0 < block111V y := by
  have hcert := block111RightChunk000Certificate_eq_true
  unfold block111RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block111RightChunk000) (lo := block111RightChunk000L) (hi := block111RightChunk000R)
    (w1 := block111W1) (w2 := block111W2) (w3 := block111W3) (w4 := block111W4)
    (s1 := block111S1) (s2 := block111S2) (s3 := block111S3) (s4 := block111S4)
    hboxes hcover block111RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block111_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block111RightL : ℝ) (block111RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block111S1 : ℝ))
    (hy2ne : y ≠ (block111S2 : ℝ))
    (hy3ne : y ≠ (block111S3 : ℝ))
    (hy4ne : y ≠ (block111S4 : ℝ)) :
    0 < block111V y := by
  have hL : (block111RightChunk000L : ℝ) = (block111RightL : ℝ) := by
    norm_num [block111RightChunk000L, block111RightL]
  have hR : (block111RightChunk000R : ℝ) = (block111RightR : ℝ) := by
    norm_num [block111RightChunk000R, block111RightR]
  have hyc : y ∈ Icc (block111RightChunk000L : ℝ) (block111RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block111_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block111_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block111LeftL : ℝ) (block111LeftR : ℝ) →
    y ≠ 0 → y ≠ (block111S1 : ℝ) → y ≠ (block111S2 : ℝ) →
    y ≠ (block111S3 : ℝ) → y ≠ (block111S4 : ℝ) → 0 < block111V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block111RightL : ℝ) (block111RightR : ℝ) →
    y ≠ 0 → y ≠ (block111S1 : ℝ) → y ≠ (block111S2 : ℝ) →
    y ≠ (block111S3 : ℝ) → y ≠ (block111S4 : ℝ) → 0 < block111V y)

theorem block111_reallog_certificate_proof :
    block111_reallog_certificate := by
  exact ⟨block111_left_V_pos, block111_right_V_pos⟩

end Block111
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block111.block111V
#check Erdos1038Lean.M1817475.Block111.block111_left_V_pos
#check Erdos1038Lean.M1817475.Block111.block111_right_V_pos
#check Erdos1038Lean.M1817475.Block111.block111_reallog_certificate_proof
