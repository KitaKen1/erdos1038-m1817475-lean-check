import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block022

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block022

open Set

def block022W1 : Rat := ((708872148992383 : Rat) / 312500000000000)
def block022W2 : Rat := (0 : Rat)
def block022W3 : Rat := (0 : Rat)
def block022W4 : Rat := ((72183428208141 : Rat) / 250000000000000)
def block022S1 : Rat := ((18174751 : Rat) / 10000000)
def block022S2 : Rat := ((511587 : Rat) / 200000)
def block022S3 : Rat := ((107000619 : Rat) / 40000000)
def block022S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block022V (y : ℝ) : ℝ :=
  ratPotential block022W1 block022W2 block022W3 block022W4 block022S1 block022S2 block022S3 block022S4 y

def block022LeftParamsCertificate : Bool :=
  allBoxesSameParams block022LeftBoxes block022W1 block022W2 block022W3 block022W4 block022S1 block022S2 block022S3 block022S4

theorem block022LeftParamsCertificate_eq_true :
    block022LeftParamsCertificate = true := by
  native_decide

theorem block022_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block022LeftL : ℝ) (block022LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block022S1 : ℝ))
    (hy2ne : y ≠ (block022S2 : ℝ))
    (hy3ne : y ≠ (block022S3 : ℝ))
    (hy4ne : y ≠ (block022S4 : ℝ)) :
    0 < block022V y := by
  have hcert := block022LeftCertificate_eq_true
  unfold block022LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block022LeftBoxes) (lo := block022LeftL) (hi := block022LeftR)
    (w1 := block022W1) (w2 := block022W2) (w3 := block022W3) (w4 := block022W4)
    (s1 := block022S1) (s2 := block022S2) (s3 := block022S3) (s4 := block022S4)
    hboxes hcover block022LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block022RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block022RightChunk000 block022W1 block022W2 block022W3 block022W4 block022S1 block022S2 block022S3 block022S4

theorem block022RightChunk000ParamsCertificate_eq_true :
    block022RightChunk000ParamsCertificate = true := by
  native_decide

theorem block022_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block022RightChunk000L : ℝ) (block022RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block022S1 : ℝ))
    (hy2ne : y ≠ (block022S2 : ℝ))
    (hy3ne : y ≠ (block022S3 : ℝ))
    (hy4ne : y ≠ (block022S4 : ℝ)) :
    0 < block022V y := by
  have hcert := block022RightChunk000Certificate_eq_true
  unfold block022RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block022RightChunk000) (lo := block022RightChunk000L) (hi := block022RightChunk000R)
    (w1 := block022W1) (w2 := block022W2) (w3 := block022W3) (w4 := block022W4)
    (s1 := block022S1) (s2 := block022S2) (s3 := block022S3) (s4 := block022S4)
    hboxes hcover block022RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block022RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block022RightChunk001 block022W1 block022W2 block022W3 block022W4 block022S1 block022S2 block022S3 block022S4

theorem block022RightChunk001ParamsCertificate_eq_true :
    block022RightChunk001ParamsCertificate = true := by
  native_decide

theorem block022_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block022RightChunk001L : ℝ) (block022RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block022S1 : ℝ))
    (hy2ne : y ≠ (block022S2 : ℝ))
    (hy3ne : y ≠ (block022S3 : ℝ))
    (hy4ne : y ≠ (block022S4 : ℝ)) :
    0 < block022V y := by
  have hcert := block022RightChunk001Certificate_eq_true
  unfold block022RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block022RightChunk001) (lo := block022RightChunk001L) (hi := block022RightChunk001R)
    (w1 := block022W1) (w2 := block022W2) (w3 := block022W3) (w4 := block022W4)
    (s1 := block022S1) (s2 := block022S2) (s3 := block022S3) (s4 := block022S4)
    hboxes hcover block022RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block022_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block022RightL : ℝ) (block022RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block022S1 : ℝ))
    (hy2ne : y ≠ (block022S2 : ℝ))
    (hy3ne : y ≠ (block022S3 : ℝ))
    (hy4ne : y ≠ (block022S4 : ℝ)) :
    0 < block022V y := by
  by_cases h0 : y ≤ (block022RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block022RightChunk000L : ℝ) (block022RightChunk000R : ℝ) := by
      have hL : (block022RightChunk000L : ℝ) = (block022RightL : ℝ) := by
        norm_num [block022RightChunk000L, block022RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block022_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block022RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block022RightChunk001L : ℝ) = (block022RightChunk000R : ℝ) := by
      norm_num [block022RightChunk001L, block022RightChunk000R]
    have hR : (block022RightChunk001R : ℝ) = (block022RightR : ℝ) := by
      norm_num [block022RightChunk001R, block022RightR]
    have hyc : y ∈ Icc (block022RightChunk001L : ℝ) (block022RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block022_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block022_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block022LeftL : ℝ) (block022LeftR : ℝ) →
    y ≠ 0 → y ≠ (block022S1 : ℝ) → y ≠ (block022S2 : ℝ) →
    y ≠ (block022S3 : ℝ) → y ≠ (block022S4 : ℝ) → 0 < block022V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block022RightL : ℝ) (block022RightR : ℝ) →
    y ≠ 0 → y ≠ (block022S1 : ℝ) → y ≠ (block022S2 : ℝ) →
    y ≠ (block022S3 : ℝ) → y ≠ (block022S4 : ℝ) → 0 < block022V y)

theorem block022_reallog_certificate_proof :
    block022_reallog_certificate := by
  exact ⟨block022_left_V_pos, block022_right_V_pos⟩

end Block022
end M1817475
end Erdos1038Lean
