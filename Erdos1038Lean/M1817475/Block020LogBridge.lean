import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block020

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block020

open Set

def block020W1 : Rat := ((22438768225380343 : Rat) / 10000000000000000)
def block020W2 : Rat := (0 : Rat)
def block020W3 : Rat := (0 : Rat)
def block020W4 : Rat := ((2900605649036477 : Rat) / 10000000000000000)
def block020S1 : Rat := ((18174751 : Rat) / 10000000)
def block020S2 : Rat := ((511587 : Rat) / 200000)
def block020S3 : Rat := ((107000619 : Rat) / 40000000)
def block020S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block020V (y : ℝ) : ℝ :=
  ratPotential block020W1 block020W2 block020W3 block020W4 block020S1 block020S2 block020S3 block020S4 y

def block020LeftParamsCertificate : Bool :=
  allBoxesSameParams block020LeftBoxes block020W1 block020W2 block020W3 block020W4 block020S1 block020S2 block020S3 block020S4

theorem block020LeftParamsCertificate_eq_true :
    block020LeftParamsCertificate = true := by
  native_decide

theorem block020_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block020LeftL : ℝ) (block020LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block020S1 : ℝ))
    (hy2ne : y ≠ (block020S2 : ℝ))
    (hy3ne : y ≠ (block020S3 : ℝ))
    (hy4ne : y ≠ (block020S4 : ℝ)) :
    0 < block020V y := by
  have hcert := block020LeftCertificate_eq_true
  unfold block020LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block020LeftBoxes) (lo := block020LeftL) (hi := block020LeftR)
    (w1 := block020W1) (w2 := block020W2) (w3 := block020W3) (w4 := block020W4)
    (s1 := block020S1) (s2 := block020S2) (s3 := block020S3) (s4 := block020S4)
    hboxes hcover block020LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block020RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block020RightChunk000 block020W1 block020W2 block020W3 block020W4 block020S1 block020S2 block020S3 block020S4

theorem block020RightChunk000ParamsCertificate_eq_true :
    block020RightChunk000ParamsCertificate = true := by
  native_decide

theorem block020_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block020RightChunk000L : ℝ) (block020RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block020S1 : ℝ))
    (hy2ne : y ≠ (block020S2 : ℝ))
    (hy3ne : y ≠ (block020S3 : ℝ))
    (hy4ne : y ≠ (block020S4 : ℝ)) :
    0 < block020V y := by
  have hcert := block020RightChunk000Certificate_eq_true
  unfold block020RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block020RightChunk000) (lo := block020RightChunk000L) (hi := block020RightChunk000R)
    (w1 := block020W1) (w2 := block020W2) (w3 := block020W3) (w4 := block020W4)
    (s1 := block020S1) (s2 := block020S2) (s3 := block020S3) (s4 := block020S4)
    hboxes hcover block020RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block020RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block020RightChunk001 block020W1 block020W2 block020W3 block020W4 block020S1 block020S2 block020S3 block020S4

theorem block020RightChunk001ParamsCertificate_eq_true :
    block020RightChunk001ParamsCertificate = true := by
  native_decide

theorem block020_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block020RightChunk001L : ℝ) (block020RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block020S1 : ℝ))
    (hy2ne : y ≠ (block020S2 : ℝ))
    (hy3ne : y ≠ (block020S3 : ℝ))
    (hy4ne : y ≠ (block020S4 : ℝ)) :
    0 < block020V y := by
  have hcert := block020RightChunk001Certificate_eq_true
  unfold block020RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block020RightChunk001) (lo := block020RightChunk001L) (hi := block020RightChunk001R)
    (w1 := block020W1) (w2 := block020W2) (w3 := block020W3) (w4 := block020W4)
    (s1 := block020S1) (s2 := block020S2) (s3 := block020S3) (s4 := block020S4)
    hboxes hcover block020RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block020_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block020RightL : ℝ) (block020RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block020S1 : ℝ))
    (hy2ne : y ≠ (block020S2 : ℝ))
    (hy3ne : y ≠ (block020S3 : ℝ))
    (hy4ne : y ≠ (block020S4 : ℝ)) :
    0 < block020V y := by
  by_cases h0 : y ≤ (block020RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block020RightChunk000L : ℝ) (block020RightChunk000R : ℝ) := by
      have hL : (block020RightChunk000L : ℝ) = (block020RightL : ℝ) := by
        norm_num [block020RightChunk000L, block020RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block020_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block020RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block020RightChunk001L : ℝ) = (block020RightChunk000R : ℝ) := by
      norm_num [block020RightChunk001L, block020RightChunk000R]
    have hR : (block020RightChunk001R : ℝ) = (block020RightR : ℝ) := by
      norm_num [block020RightChunk001R, block020RightR]
    have hyc : y ∈ Icc (block020RightChunk001L : ℝ) (block020RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block020_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block020_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block020LeftL : ℝ) (block020LeftR : ℝ) →
    y ≠ 0 → y ≠ (block020S1 : ℝ) → y ≠ (block020S2 : ℝ) →
    y ≠ (block020S3 : ℝ) → y ≠ (block020S4 : ℝ) → 0 < block020V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block020RightL : ℝ) (block020RightR : ℝ) →
    y ≠ 0 → y ≠ (block020S1 : ℝ) → y ≠ (block020S2 : ℝ) →
    y ≠ (block020S3 : ℝ) → y ≠ (block020S4 : ℝ) → 0 < block020V y)

theorem block020_reallog_certificate_proof :
    block020_reallog_certificate := by
  exact ⟨block020_left_V_pos, block020_right_V_pos⟩

end Block020
end M1817475
end Erdos1038Lean
