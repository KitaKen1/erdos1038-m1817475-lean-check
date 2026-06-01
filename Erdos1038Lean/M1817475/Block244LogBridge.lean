import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block244

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block244

open Set

def block244W1 : Rat := ((1072618343894593 : Rat) / 1250000000000000)
def block244W2 : Rat := ((1066664010314727 : Rat) / 12500000000000000)
def block244W3 : Rat := ((4063124218112141 : Rat) / 100000000000000000)
def block244W4 : Rat := ((2107224938253153 : Rat) / 10000000000000000)
def block244S1 : Rat := ((18174751 : Rat) / 10000000)
def block244S2 : Rat := ((511587 : Rat) / 200000)
def block244S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block244S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block244V (y : ℝ) : ℝ :=
  ratPotential block244W1 block244W2 block244W3 block244W4 block244S1 block244S2 block244S3 block244S4 y

def block244LeftParamsCertificate : Bool :=
  allBoxesSameParams block244LeftBoxes block244W1 block244W2 block244W3 block244W4 block244S1 block244S2 block244S3 block244S4

theorem block244LeftParamsCertificate_eq_true :
    block244LeftParamsCertificate = true := by
  native_decide

theorem block244_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block244LeftL : ℝ) (block244LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block244S1 : ℝ))
    (hy2ne : y ≠ (block244S2 : ℝ))
    (hy3ne : y ≠ (block244S3 : ℝ))
    (hy4ne : y ≠ (block244S4 : ℝ)) :
    0 < block244V y := by
  have hcert := block244LeftCertificate_eq_true
  unfold block244LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block244LeftBoxes) (lo := block244LeftL) (hi := block244LeftR)
    (w1 := block244W1) (w2 := block244W2) (w3 := block244W3) (w4 := block244W4)
    (s1 := block244S1) (s2 := block244S2) (s3 := block244S3) (s4 := block244S4)
    hboxes hcover block244LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block244RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block244RightChunk000 block244W1 block244W2 block244W3 block244W4 block244S1 block244S2 block244S3 block244S4

theorem block244RightChunk000ParamsCertificate_eq_true :
    block244RightChunk000ParamsCertificate = true := by
  native_decide

theorem block244_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block244RightChunk000L : ℝ) (block244RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block244S1 : ℝ))
    (hy2ne : y ≠ (block244S2 : ℝ))
    (hy3ne : y ≠ (block244S3 : ℝ))
    (hy4ne : y ≠ (block244S4 : ℝ)) :
    0 < block244V y := by
  have hcert := block244RightChunk000Certificate_eq_true
  unfold block244RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block244RightChunk000) (lo := block244RightChunk000L) (hi := block244RightChunk000R)
    (w1 := block244W1) (w2 := block244W2) (w3 := block244W3) (w4 := block244W4)
    (s1 := block244S1) (s2 := block244S2) (s3 := block244S3) (s4 := block244S4)
    hboxes hcover block244RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block244RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block244RightChunk001 block244W1 block244W2 block244W3 block244W4 block244S1 block244S2 block244S3 block244S4

theorem block244RightChunk001ParamsCertificate_eq_true :
    block244RightChunk001ParamsCertificate = true := by
  native_decide

theorem block244_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block244RightChunk001L : ℝ) (block244RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block244S1 : ℝ))
    (hy2ne : y ≠ (block244S2 : ℝ))
    (hy3ne : y ≠ (block244S3 : ℝ))
    (hy4ne : y ≠ (block244S4 : ℝ)) :
    0 < block244V y := by
  have hcert := block244RightChunk001Certificate_eq_true
  unfold block244RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block244RightChunk001) (lo := block244RightChunk001L) (hi := block244RightChunk001R)
    (w1 := block244W1) (w2 := block244W2) (w3 := block244W3) (w4 := block244W4)
    (s1 := block244S1) (s2 := block244S2) (s3 := block244S3) (s4 := block244S4)
    hboxes hcover block244RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block244_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block244RightL : ℝ) (block244RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block244S1 : ℝ))
    (hy2ne : y ≠ (block244S2 : ℝ))
    (hy3ne : y ≠ (block244S3 : ℝ))
    (hy4ne : y ≠ (block244S4 : ℝ)) :
    0 < block244V y := by
  by_cases h0 : y ≤ (block244RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block244RightChunk000L : ℝ) (block244RightChunk000R : ℝ) := by
      have hL : (block244RightChunk000L : ℝ) = (block244RightL : ℝ) := by
        norm_num [block244RightChunk000L, block244RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block244_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block244RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block244RightChunk001L : ℝ) = (block244RightChunk000R : ℝ) := by
      norm_num [block244RightChunk001L, block244RightChunk000R]
    have hR : (block244RightChunk001R : ℝ) = (block244RightR : ℝ) := by
      norm_num [block244RightChunk001R, block244RightR]
    have hyc : y ∈ Icc (block244RightChunk001L : ℝ) (block244RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block244_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block244_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block244LeftL : ℝ) (block244LeftR : ℝ) →
    y ≠ 0 → y ≠ (block244S1 : ℝ) → y ≠ (block244S2 : ℝ) →
    y ≠ (block244S3 : ℝ) → y ≠ (block244S4 : ℝ) → 0 < block244V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block244RightL : ℝ) (block244RightR : ℝ) →
    y ≠ 0 → y ≠ (block244S1 : ℝ) → y ≠ (block244S2 : ℝ) →
    y ≠ (block244S3 : ℝ) → y ≠ (block244S4 : ℝ) → 0 < block244V y)

theorem block244_reallog_certificate_proof :
    block244_reallog_certificate := by
  exact ⟨block244_left_V_pos, block244_right_V_pos⟩

end Block244
end M1817475
end Erdos1038Lean
