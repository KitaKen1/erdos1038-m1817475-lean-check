import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block058

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block058

open Set

def block058W1 : Rat := ((14121666026212951 : Rat) / 5000000000000000)
def block058W2 : Rat := (0 : Rat)
def block058W3 : Rat := (0 : Rat)
def block058W4 : Rat := ((26198846287398997 : Rat) / 100000000000000000)
def block058S1 : Rat := ((18174751 : Rat) / 10000000)
def block058S2 : Rat := ((511587 : Rat) / 200000)
def block058S3 : Rat := ((107000619 : Rat) / 40000000)
def block058S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block058V (y : ℝ) : ℝ :=
  ratPotential block058W1 block058W2 block058W3 block058W4 block058S1 block058S2 block058S3 block058S4 y

def block058LeftParamsCertificate : Bool :=
  allBoxesSameParams block058LeftBoxes block058W1 block058W2 block058W3 block058W4 block058S1 block058S2 block058S3 block058S4

theorem block058LeftParamsCertificate_eq_true :
    block058LeftParamsCertificate = true := by
  native_decide

theorem block058_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block058LeftL : ℝ) (block058LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block058S1 : ℝ))
    (hy2ne : y ≠ (block058S2 : ℝ))
    (hy3ne : y ≠ (block058S3 : ℝ))
    (hy4ne : y ≠ (block058S4 : ℝ)) :
    0 < block058V y := by
  have hcert := block058LeftCertificate_eq_true
  unfold block058LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block058LeftBoxes) (lo := block058LeftL) (hi := block058LeftR)
    (w1 := block058W1) (w2 := block058W2) (w3 := block058W3) (w4 := block058W4)
    (s1 := block058S1) (s2 := block058S2) (s3 := block058S3) (s4 := block058S4)
    hboxes hcover block058LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block058RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block058RightChunk000 block058W1 block058W2 block058W3 block058W4 block058S1 block058S2 block058S3 block058S4

theorem block058RightChunk000ParamsCertificate_eq_true :
    block058RightChunk000ParamsCertificate = true := by
  native_decide

theorem block058_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block058RightChunk000L : ℝ) (block058RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block058S1 : ℝ))
    (hy2ne : y ≠ (block058S2 : ℝ))
    (hy3ne : y ≠ (block058S3 : ℝ))
    (hy4ne : y ≠ (block058S4 : ℝ)) :
    0 < block058V y := by
  have hcert := block058RightChunk000Certificate_eq_true
  unfold block058RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block058RightChunk000) (lo := block058RightChunk000L) (hi := block058RightChunk000R)
    (w1 := block058W1) (w2 := block058W2) (w3 := block058W3) (w4 := block058W4)
    (s1 := block058S1) (s2 := block058S2) (s3 := block058S3) (s4 := block058S4)
    hboxes hcover block058RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block058_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block058RightL : ℝ) (block058RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block058S1 : ℝ))
    (hy2ne : y ≠ (block058S2 : ℝ))
    (hy3ne : y ≠ (block058S3 : ℝ))
    (hy4ne : y ≠ (block058S4 : ℝ)) :
    0 < block058V y := by
  have hL : (block058RightChunk000L : ℝ) = (block058RightL : ℝ) := by
    norm_num [block058RightChunk000L, block058RightL]
  have hR : (block058RightChunk000R : ℝ) = (block058RightR : ℝ) := by
    norm_num [block058RightChunk000R, block058RightR]
  have hyc : y ∈ Icc (block058RightChunk000L : ℝ) (block058RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block058_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block058_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block058LeftL : ℝ) (block058LeftR : ℝ) →
    y ≠ 0 → y ≠ (block058S1 : ℝ) → y ≠ (block058S2 : ℝ) →
    y ≠ (block058S3 : ℝ) → y ≠ (block058S4 : ℝ) → 0 < block058V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block058RightL : ℝ) (block058RightR : ℝ) →
    y ≠ 0 → y ≠ (block058S1 : ℝ) → y ≠ (block058S2 : ℝ) →
    y ≠ (block058S3 : ℝ) → y ≠ (block058S4 : ℝ) → 0 < block058V y)

theorem block058_reallog_certificate_proof :
    block058_reallog_certificate := by
  exact ⟨block058_left_V_pos, block058_right_V_pos⟩

end Block058
end M1817475
end Erdos1038Lean
