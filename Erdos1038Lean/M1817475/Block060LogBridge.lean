import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block060

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block060

open Set

def block060W1 : Rat := ((2863482747309151 : Rat) / 1000000000000000)
def block060W2 : Rat := (0 : Rat)
def block060W3 : Rat := (0 : Rat)
def block060W4 : Rat := ((26030861972511343 : Rat) / 100000000000000000)
def block060S1 : Rat := ((18174751 : Rat) / 10000000)
def block060S2 : Rat := ((511587 : Rat) / 200000)
def block060S3 : Rat := ((107000619 : Rat) / 40000000)
def block060S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block060V (y : ℝ) : ℝ :=
  ratPotential block060W1 block060W2 block060W3 block060W4 block060S1 block060S2 block060S3 block060S4 y

def block060LeftParamsCertificate : Bool :=
  allBoxesSameParams block060LeftBoxes block060W1 block060W2 block060W3 block060W4 block060S1 block060S2 block060S3 block060S4

theorem block060LeftParamsCertificate_eq_true :
    block060LeftParamsCertificate = true := by
  native_decide

theorem block060_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block060LeftL : ℝ) (block060LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block060S1 : ℝ))
    (hy2ne : y ≠ (block060S2 : ℝ))
    (hy3ne : y ≠ (block060S3 : ℝ))
    (hy4ne : y ≠ (block060S4 : ℝ)) :
    0 < block060V y := by
  have hcert := block060LeftCertificate_eq_true
  unfold block060LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block060LeftBoxes) (lo := block060LeftL) (hi := block060LeftR)
    (w1 := block060W1) (w2 := block060W2) (w3 := block060W3) (w4 := block060W4)
    (s1 := block060S1) (s2 := block060S2) (s3 := block060S3) (s4 := block060S4)
    hboxes hcover block060LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block060RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block060RightChunk000 block060W1 block060W2 block060W3 block060W4 block060S1 block060S2 block060S3 block060S4

theorem block060RightChunk000ParamsCertificate_eq_true :
    block060RightChunk000ParamsCertificate = true := by
  native_decide

theorem block060_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block060RightChunk000L : ℝ) (block060RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block060S1 : ℝ))
    (hy2ne : y ≠ (block060S2 : ℝ))
    (hy3ne : y ≠ (block060S3 : ℝ))
    (hy4ne : y ≠ (block060S4 : ℝ)) :
    0 < block060V y := by
  have hcert := block060RightChunk000Certificate_eq_true
  unfold block060RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block060RightChunk000) (lo := block060RightChunk000L) (hi := block060RightChunk000R)
    (w1 := block060W1) (w2 := block060W2) (w3 := block060W3) (w4 := block060W4)
    (s1 := block060S1) (s2 := block060S2) (s3 := block060S3) (s4 := block060S4)
    hboxes hcover block060RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block060_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block060RightL : ℝ) (block060RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block060S1 : ℝ))
    (hy2ne : y ≠ (block060S2 : ℝ))
    (hy3ne : y ≠ (block060S3 : ℝ))
    (hy4ne : y ≠ (block060S4 : ℝ)) :
    0 < block060V y := by
  have hL : (block060RightChunk000L : ℝ) = (block060RightL : ℝ) := by
    norm_num [block060RightChunk000L, block060RightL]
  have hR : (block060RightChunk000R : ℝ) = (block060RightR : ℝ) := by
    norm_num [block060RightChunk000R, block060RightR]
  have hyc : y ∈ Icc (block060RightChunk000L : ℝ) (block060RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block060_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block060_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block060LeftL : ℝ) (block060LeftR : ℝ) →
    y ≠ 0 → y ≠ (block060S1 : ℝ) → y ≠ (block060S2 : ℝ) →
    y ≠ (block060S3 : ℝ) → y ≠ (block060S4 : ℝ) → 0 < block060V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block060RightL : ℝ) (block060RightR : ℝ) →
    y ≠ 0 → y ≠ (block060S1 : ℝ) → y ≠ (block060S2 : ℝ) →
    y ≠ (block060S3 : ℝ) → y ≠ (block060S4 : ℝ) → 0 < block060V y)

theorem block060_reallog_certificate_proof :
    block060_reallog_certificate := by
  exact ⟨block060_left_V_pos, block060_right_V_pos⟩

end Block060
end M1817475
end Erdos1038Lean
