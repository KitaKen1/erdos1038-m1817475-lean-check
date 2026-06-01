import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block480

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block480

open Set

def block480W1 : Rat := ((5145353083630531 : Rat) / 10000000000000000)
def block480W2 : Rat := (0 : Rat)
def block480W3 : Rat := ((118172270275279 : Rat) / 312500000000000)
def block480W4 : Rat := ((4207263507615127 : Rat) / 100000000000000000)
def block480S1 : Rat := ((18174751 : Rat) / 10000000)
def block480S2 : Rat := ((511587 : Rat) / 200000)
def block480S3 : Rat := ((130749985803571428703 : Rat) / 50000000000000000000)
def block480S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block480V (y : ℝ) : ℝ :=
  ratPotential block480W1 block480W2 block480W3 block480W4 block480S1 block480S2 block480S3 block480S4 y

def block480LeftParamsCertificate : Bool :=
  allBoxesSameParams block480LeftBoxes block480W1 block480W2 block480W3 block480W4 block480S1 block480S2 block480S3 block480S4

theorem block480LeftParamsCertificate_eq_true :
    block480LeftParamsCertificate = true := by
  native_decide

theorem block480_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block480LeftL : ℝ) (block480LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block480S1 : ℝ))
    (hy2ne : y ≠ (block480S2 : ℝ))
    (hy3ne : y ≠ (block480S3 : ℝ))
    (hy4ne : y ≠ (block480S4 : ℝ)) :
    0 < block480V y := by
  have hcert := block480LeftCertificate_eq_true
  unfold block480LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block480LeftBoxes) (lo := block480LeftL) (hi := block480LeftR)
    (w1 := block480W1) (w2 := block480W2) (w3 := block480W3) (w4 := block480W4)
    (s1 := block480S1) (s2 := block480S2) (s3 := block480S3) (s4 := block480S4)
    hboxes hcover block480LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block480RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block480RightChunk000 block480W1 block480W2 block480W3 block480W4 block480S1 block480S2 block480S3 block480S4

theorem block480RightChunk000ParamsCertificate_eq_true :
    block480RightChunk000ParamsCertificate = true := by
  native_decide

theorem block480_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block480RightChunk000L : ℝ) (block480RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block480S1 : ℝ))
    (hy2ne : y ≠ (block480S2 : ℝ))
    (hy3ne : y ≠ (block480S3 : ℝ))
    (hy4ne : y ≠ (block480S4 : ℝ)) :
    0 < block480V y := by
  have hcert := block480RightChunk000Certificate_eq_true
  unfold block480RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block480RightChunk000) (lo := block480RightChunk000L) (hi := block480RightChunk000R)
    (w1 := block480W1) (w2 := block480W2) (w3 := block480W3) (w4 := block480W4)
    (s1 := block480S1) (s2 := block480S2) (s3 := block480S3) (s4 := block480S4)
    hboxes hcover block480RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block480_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block480RightL : ℝ) (block480RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block480S1 : ℝ))
    (hy2ne : y ≠ (block480S2 : ℝ))
    (hy3ne : y ≠ (block480S3 : ℝ))
    (hy4ne : y ≠ (block480S4 : ℝ)) :
    0 < block480V y := by
  have hL : (block480RightChunk000L : ℝ) = (block480RightL : ℝ) := by
    norm_num [block480RightChunk000L, block480RightL]
  have hR : (block480RightChunk000R : ℝ) = (block480RightR : ℝ) := by
    norm_num [block480RightChunk000R, block480RightR]
  have hyc : y ∈ Icc (block480RightChunk000L : ℝ) (block480RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block480_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block480_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block480LeftL : ℝ) (block480LeftR : ℝ) →
    y ≠ 0 → y ≠ (block480S1 : ℝ) → y ≠ (block480S2 : ℝ) →
    y ≠ (block480S3 : ℝ) → y ≠ (block480S4 : ℝ) → 0 < block480V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block480RightL : ℝ) (block480RightR : ℝ) →
    y ≠ 0 → y ≠ (block480S1 : ℝ) → y ≠ (block480S2 : ℝ) →
    y ≠ (block480S3 : ℝ) → y ≠ (block480S4 : ℝ) → 0 < block480V y)

theorem block480_reallog_certificate_proof :
    block480_reallog_certificate := by
  exact ⟨block480_left_V_pos, block480_right_V_pos⟩

end Block480
end M1817475
end Erdos1038Lean
