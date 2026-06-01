import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block376

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block376

open Set

def block376W1 : Rat := ((8569118472855103 : Rat) / 10000000000000000)
def block376W2 : Rat := ((23379747537478287 : Rat) / 500000000000000000)
def block376W3 : Rat := ((7839831669628501 : Rat) / 50000000000000000)
def block376W4 : Rat := ((14015432630633687 : Rat) / 100000000000000000)
def block376S1 : Rat := ((18174751 : Rat) / 10000000)
def block376S2 : Rat := ((511587 : Rat) / 200000)
def block376S3 : Rat := ((132783092946428571471 : Rat) / 50000000000000000000)
def block376S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block376V (y : ℝ) : ℝ :=
  ratPotential block376W1 block376W2 block376W3 block376W4 block376S1 block376S2 block376S3 block376S4 y

def block376LeftParamsCertificate : Bool :=
  allBoxesSameParams block376LeftBoxes block376W1 block376W2 block376W3 block376W4 block376S1 block376S2 block376S3 block376S4

theorem block376LeftParamsCertificate_eq_true :
    block376LeftParamsCertificate = true := by
  native_decide

theorem block376_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block376LeftL : ℝ) (block376LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block376S1 : ℝ))
    (hy2ne : y ≠ (block376S2 : ℝ))
    (hy3ne : y ≠ (block376S3 : ℝ))
    (hy4ne : y ≠ (block376S4 : ℝ)) :
    0 < block376V y := by
  have hcert := block376LeftCertificate_eq_true
  unfold block376LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block376LeftBoxes) (lo := block376LeftL) (hi := block376LeftR)
    (w1 := block376W1) (w2 := block376W2) (w3 := block376W3) (w4 := block376W4)
    (s1 := block376S1) (s2 := block376S2) (s3 := block376S3) (s4 := block376S4)
    hboxes hcover block376LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block376RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block376RightChunk000 block376W1 block376W2 block376W3 block376W4 block376S1 block376S2 block376S3 block376S4

theorem block376RightChunk000ParamsCertificate_eq_true :
    block376RightChunk000ParamsCertificate = true := by
  native_decide

theorem block376_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block376RightChunk000L : ℝ) (block376RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block376S1 : ℝ))
    (hy2ne : y ≠ (block376S2 : ℝ))
    (hy3ne : y ≠ (block376S3 : ℝ))
    (hy4ne : y ≠ (block376S4 : ℝ)) :
    0 < block376V y := by
  have hcert := block376RightChunk000Certificate_eq_true
  unfold block376RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block376RightChunk000) (lo := block376RightChunk000L) (hi := block376RightChunk000R)
    (w1 := block376W1) (w2 := block376W2) (w3 := block376W3) (w4 := block376W4)
    (s1 := block376S1) (s2 := block376S2) (s3 := block376S3) (s4 := block376S4)
    hboxes hcover block376RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block376_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block376RightL : ℝ) (block376RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block376S1 : ℝ))
    (hy2ne : y ≠ (block376S2 : ℝ))
    (hy3ne : y ≠ (block376S3 : ℝ))
    (hy4ne : y ≠ (block376S4 : ℝ)) :
    0 < block376V y := by
  have hL : (block376RightChunk000L : ℝ) = (block376RightL : ℝ) := by
    norm_num [block376RightChunk000L, block376RightL]
  have hR : (block376RightChunk000R : ℝ) = (block376RightR : ℝ) := by
    norm_num [block376RightChunk000R, block376RightR]
  have hyc : y ∈ Icc (block376RightChunk000L : ℝ) (block376RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block376_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block376_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block376LeftL : ℝ) (block376LeftR : ℝ) →
    y ≠ 0 → y ≠ (block376S1 : ℝ) → y ≠ (block376S2 : ℝ) →
    y ≠ (block376S3 : ℝ) → y ≠ (block376S4 : ℝ) → 0 < block376V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block376RightL : ℝ) (block376RightR : ℝ) →
    y ≠ 0 → y ≠ (block376S1 : ℝ) → y ≠ (block376S2 : ℝ) →
    y ≠ (block376S3 : ℝ) → y ≠ (block376S4 : ℝ) → 0 < block376V y)

theorem block376_reallog_certificate_proof :
    block376_reallog_certificate := by
  exact ⟨block376_left_V_pos, block376_right_V_pos⟩

end Block376
end M1817475
end Erdos1038Lean
