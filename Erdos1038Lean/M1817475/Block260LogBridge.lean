import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block260

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block260

open Set

def block260W1 : Rat := ((1789023162186129 : Rat) / 2000000000000000)
def block260W2 : Rat := ((744114720939409 : Rat) / 10000000000000000)
def block260W3 : Rat := ((19735045742047141 : Rat) / 100000000000000000)
def block260W4 : Rat := ((6158095664940593 : Rat) / 100000000000000000)
def block260S1 : Rat := ((18174751 : Rat) / 10000000)
def block260S2 : Rat := ((511587 : Rat) / 200000)
def block260S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block260S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block260V (y : ℝ) : ℝ :=
  ratPotential block260W1 block260W2 block260W3 block260W4 block260S1 block260S2 block260S3 block260S4 y

def block260LeftParamsCertificate : Bool :=
  allBoxesSameParams block260LeftBoxes block260W1 block260W2 block260W3 block260W4 block260S1 block260S2 block260S3 block260S4

theorem block260LeftParamsCertificate_eq_true :
    block260LeftParamsCertificate = true := by
  native_decide

theorem block260_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block260LeftL : ℝ) (block260LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block260S1 : ℝ))
    (hy2ne : y ≠ (block260S2 : ℝ))
    (hy3ne : y ≠ (block260S3 : ℝ))
    (hy4ne : y ≠ (block260S4 : ℝ)) :
    0 < block260V y := by
  have hcert := block260LeftCertificate_eq_true
  unfold block260LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block260LeftBoxes) (lo := block260LeftL) (hi := block260LeftR)
    (w1 := block260W1) (w2 := block260W2) (w3 := block260W3) (w4 := block260W4)
    (s1 := block260S1) (s2 := block260S2) (s3 := block260S3) (s4 := block260S4)
    hboxes hcover block260LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block260RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block260RightChunk000 block260W1 block260W2 block260W3 block260W4 block260S1 block260S2 block260S3 block260S4

theorem block260RightChunk000ParamsCertificate_eq_true :
    block260RightChunk000ParamsCertificate = true := by
  native_decide

theorem block260_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block260RightChunk000L : ℝ) (block260RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block260S1 : ℝ))
    (hy2ne : y ≠ (block260S2 : ℝ))
    (hy3ne : y ≠ (block260S3 : ℝ))
    (hy4ne : y ≠ (block260S4 : ℝ)) :
    0 < block260V y := by
  have hcert := block260RightChunk000Certificate_eq_true
  unfold block260RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block260RightChunk000) (lo := block260RightChunk000L) (hi := block260RightChunk000R)
    (w1 := block260W1) (w2 := block260W2) (w3 := block260W3) (w4 := block260W4)
    (s1 := block260S1) (s2 := block260S2) (s3 := block260S3) (s4 := block260S4)
    hboxes hcover block260RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block260RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block260RightChunk001 block260W1 block260W2 block260W3 block260W4 block260S1 block260S2 block260S3 block260S4

theorem block260RightChunk001ParamsCertificate_eq_true :
    block260RightChunk001ParamsCertificate = true := by
  native_decide

theorem block260_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block260RightChunk001L : ℝ) (block260RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block260S1 : ℝ))
    (hy2ne : y ≠ (block260S2 : ℝ))
    (hy3ne : y ≠ (block260S3 : ℝ))
    (hy4ne : y ≠ (block260S4 : ℝ)) :
    0 < block260V y := by
  have hcert := block260RightChunk001Certificate_eq_true
  unfold block260RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block260RightChunk001) (lo := block260RightChunk001L) (hi := block260RightChunk001R)
    (w1 := block260W1) (w2 := block260W2) (w3 := block260W3) (w4 := block260W4)
    (s1 := block260S1) (s2 := block260S2) (s3 := block260S3) (s4 := block260S4)
    hboxes hcover block260RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block260_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block260RightL : ℝ) (block260RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block260S1 : ℝ))
    (hy2ne : y ≠ (block260S2 : ℝ))
    (hy3ne : y ≠ (block260S3 : ℝ))
    (hy4ne : y ≠ (block260S4 : ℝ)) :
    0 < block260V y := by
  by_cases h0 : y ≤ (block260RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block260RightChunk000L : ℝ) (block260RightChunk000R : ℝ) := by
      have hL : (block260RightChunk000L : ℝ) = (block260RightL : ℝ) := by
        norm_num [block260RightChunk000L, block260RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block260_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block260RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block260RightChunk001L : ℝ) = (block260RightChunk000R : ℝ) := by
      norm_num [block260RightChunk001L, block260RightChunk000R]
    have hR : (block260RightChunk001R : ℝ) = (block260RightR : ℝ) := by
      norm_num [block260RightChunk001R, block260RightR]
    have hyc : y ∈ Icc (block260RightChunk001L : ℝ) (block260RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block260_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block260_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block260LeftL : ℝ) (block260LeftR : ℝ) →
    y ≠ 0 → y ≠ (block260S1 : ℝ) → y ≠ (block260S2 : ℝ) →
    y ≠ (block260S3 : ℝ) → y ≠ (block260S4 : ℝ) → 0 < block260V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block260RightL : ℝ) (block260RightR : ℝ) →
    y ≠ 0 → y ≠ (block260S1 : ℝ) → y ≠ (block260S2 : ℝ) →
    y ≠ (block260S3 : ℝ) → y ≠ (block260S4 : ℝ) → 0 < block260V y)

theorem block260_reallog_certificate_proof :
    block260_reallog_certificate := by
  exact ⟨block260_left_V_pos, block260_right_V_pos⟩

end Block260
end M1817475
end Erdos1038Lean
