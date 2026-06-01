import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block512

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block512

open Set

def block512W1 : Rat := ((2152357320106879 : Rat) / 5000000000000000)
def block512W2 : Rat := (0 : Rat)
def block512W3 : Rat := ((2204376616122697 : Rat) / 5000000000000000)
def block512W4 : Rat := ((34738104720721903 : Rat) / 10000000000000000000)
def block512S1 : Rat := ((18174751 : Rat) / 10000000)
def block512S2 : Rat := ((511587 : Rat) / 200000)
def block512S3 : Rat := ((130124414375000000159 : Rat) / 50000000000000000000)
def block512S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block512V (y : ℝ) : ℝ :=
  ratPotential block512W1 block512W2 block512W3 block512W4 block512S1 block512S2 block512S3 block512S4 y

def block512LeftParamsCertificate : Bool :=
  allBoxesSameParams block512LeftBoxes block512W1 block512W2 block512W3 block512W4 block512S1 block512S2 block512S3 block512S4

theorem block512LeftParamsCertificate_eq_true :
    block512LeftParamsCertificate = true := by
  native_decide

theorem block512_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block512LeftL : ℝ) (block512LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block512S1 : ℝ))
    (hy2ne : y ≠ (block512S2 : ℝ))
    (hy3ne : y ≠ (block512S3 : ℝ))
    (hy4ne : y ≠ (block512S4 : ℝ)) :
    0 < block512V y := by
  have hcert := block512LeftCertificate_eq_true
  unfold block512LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block512LeftBoxes) (lo := block512LeftL) (hi := block512LeftR)
    (w1 := block512W1) (w2 := block512W2) (w3 := block512W3) (w4 := block512W4)
    (s1 := block512S1) (s2 := block512S2) (s3 := block512S3) (s4 := block512S4)
    hboxes hcover block512LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block512RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block512RightChunk000 block512W1 block512W2 block512W3 block512W4 block512S1 block512S2 block512S3 block512S4

theorem block512RightChunk000ParamsCertificate_eq_true :
    block512RightChunk000ParamsCertificate = true := by
  native_decide

theorem block512_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block512RightChunk000L : ℝ) (block512RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block512S1 : ℝ))
    (hy2ne : y ≠ (block512S2 : ℝ))
    (hy3ne : y ≠ (block512S3 : ℝ))
    (hy4ne : y ≠ (block512S4 : ℝ)) :
    0 < block512V y := by
  have hcert := block512RightChunk000Certificate_eq_true
  unfold block512RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block512RightChunk000) (lo := block512RightChunk000L) (hi := block512RightChunk000R)
    (w1 := block512W1) (w2 := block512W2) (w3 := block512W3) (w4 := block512W4)
    (s1 := block512S1) (s2 := block512S2) (s3 := block512S3) (s4 := block512S4)
    hboxes hcover block512RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block512_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block512RightL : ℝ) (block512RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block512S1 : ℝ))
    (hy2ne : y ≠ (block512S2 : ℝ))
    (hy3ne : y ≠ (block512S3 : ℝ))
    (hy4ne : y ≠ (block512S4 : ℝ)) :
    0 < block512V y := by
  have hL : (block512RightChunk000L : ℝ) = (block512RightL : ℝ) := by
    norm_num [block512RightChunk000L, block512RightL]
  have hR : (block512RightChunk000R : ℝ) = (block512RightR : ℝ) := by
    norm_num [block512RightChunk000R, block512RightR]
  have hyc : y ∈ Icc (block512RightChunk000L : ℝ) (block512RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block512_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block512_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block512LeftL : ℝ) (block512LeftR : ℝ) →
    y ≠ 0 → y ≠ (block512S1 : ℝ) → y ≠ (block512S2 : ℝ) →
    y ≠ (block512S3 : ℝ) → y ≠ (block512S4 : ℝ) → 0 < block512V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block512RightL : ℝ) (block512RightR : ℝ) →
    y ≠ 0 → y ≠ (block512S1 : ℝ) → y ≠ (block512S2 : ℝ) →
    y ≠ (block512S3 : ℝ) → y ≠ (block512S4 : ℝ) → 0 < block512V y)

theorem block512_reallog_certificate_proof :
    block512_reallog_certificate := by
  exact ⟨block512_left_V_pos, block512_right_V_pos⟩

end Block512
end M1817475
end Erdos1038Lean
