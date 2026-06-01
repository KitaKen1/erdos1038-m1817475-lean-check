import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block341

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block341

open Set

def block341W1 : Rat := ((4626073036365903 : Rat) / 5000000000000000)
def block341W2 : Rat := ((2372598354655021 : Rat) / 50000000000000000)
def block341W3 : Rat := ((14645705497254857 : Rat) / 100000000000000000)
def block341W4 : Rat := ((1375697255376239 : Rat) / 10000000000000000)
def block341S1 : Rat := ((18174751 : Rat) / 10000000)
def block341S2 : Rat := ((511587 : Rat) / 200000)
def block341S3 : Rat := ((133467311696428571441 : Rat) / 50000000000000000000)
def block341S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block341V (y : ℝ) : ℝ :=
  ratPotential block341W1 block341W2 block341W3 block341W4 block341S1 block341S2 block341S3 block341S4 y

def block341LeftParamsCertificate : Bool :=
  allBoxesSameParams block341LeftBoxes block341W1 block341W2 block341W3 block341W4 block341S1 block341S2 block341S3 block341S4

theorem block341LeftParamsCertificate_eq_true :
    block341LeftParamsCertificate = true := by
  native_decide

theorem block341_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block341LeftL : ℝ) (block341LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block341S1 : ℝ))
    (hy2ne : y ≠ (block341S2 : ℝ))
    (hy3ne : y ≠ (block341S3 : ℝ))
    (hy4ne : y ≠ (block341S4 : ℝ)) :
    0 < block341V y := by
  have hcert := block341LeftCertificate_eq_true
  unfold block341LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block341LeftBoxes) (lo := block341LeftL) (hi := block341LeftR)
    (w1 := block341W1) (w2 := block341W2) (w3 := block341W3) (w4 := block341W4)
    (s1 := block341S1) (s2 := block341S2) (s3 := block341S3) (s4 := block341S4)
    hboxes hcover block341LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block341RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block341RightChunk000 block341W1 block341W2 block341W3 block341W4 block341S1 block341S2 block341S3 block341S4

theorem block341RightChunk000ParamsCertificate_eq_true :
    block341RightChunk000ParamsCertificate = true := by
  native_decide

theorem block341_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block341RightChunk000L : ℝ) (block341RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block341S1 : ℝ))
    (hy2ne : y ≠ (block341S2 : ℝ))
    (hy3ne : y ≠ (block341S3 : ℝ))
    (hy4ne : y ≠ (block341S4 : ℝ)) :
    0 < block341V y := by
  have hcert := block341RightChunk000Certificate_eq_true
  unfold block341RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block341RightChunk000) (lo := block341RightChunk000L) (hi := block341RightChunk000R)
    (w1 := block341W1) (w2 := block341W2) (w3 := block341W3) (w4 := block341W4)
    (s1 := block341S1) (s2 := block341S2) (s3 := block341S3) (s4 := block341S4)
    hboxes hcover block341RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block341_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block341RightL : ℝ) (block341RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block341S1 : ℝ))
    (hy2ne : y ≠ (block341S2 : ℝ))
    (hy3ne : y ≠ (block341S3 : ℝ))
    (hy4ne : y ≠ (block341S4 : ℝ)) :
    0 < block341V y := by
  have hL : (block341RightChunk000L : ℝ) = (block341RightL : ℝ) := by
    norm_num [block341RightChunk000L, block341RightL]
  have hR : (block341RightChunk000R : ℝ) = (block341RightR : ℝ) := by
    norm_num [block341RightChunk000R, block341RightR]
  have hyc : y ∈ Icc (block341RightChunk000L : ℝ) (block341RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block341_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block341_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block341LeftL : ℝ) (block341LeftR : ℝ) →
    y ≠ 0 → y ≠ (block341S1 : ℝ) → y ≠ (block341S2 : ℝ) →
    y ≠ (block341S3 : ℝ) → y ≠ (block341S4 : ℝ) → 0 < block341V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block341RightL : ℝ) (block341RightR : ℝ) →
    y ≠ 0 → y ≠ (block341S1 : ℝ) → y ≠ (block341S2 : ℝ) →
    y ≠ (block341S3 : ℝ) → y ≠ (block341S4 : ℝ) → 0 < block341V y)

theorem block341_reallog_certificate_proof :
    block341_reallog_certificate := by
  exact ⟨block341_left_V_pos, block341_right_V_pos⟩

end Block341
end M1817475
end Erdos1038Lean
