import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block107

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block107

open Set

def block107W1 : Rat := ((258534281390109 : Rat) / 100000000000000)
def block107W2 : Rat := (0 : Rat)
def block107W3 : Rat := ((36319050911311 : Rat) / 625000000000000)
def block107W4 : Rat := ((469840813775251 : Rat) / 2500000000000000)
def block107S1 : Rat := ((18174751 : Rat) / 10000000)
def block107S2 : Rat := ((511587 : Rat) / 200000)
def block107S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block107S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block107V (y : ℝ) : ℝ :=
  ratPotential block107W1 block107W2 block107W3 block107W4 block107S1 block107S2 block107S3 block107S4 y

def block107LeftParamsCertificate : Bool :=
  allBoxesSameParams block107LeftBoxes block107W1 block107W2 block107W3 block107W4 block107S1 block107S2 block107S3 block107S4

theorem block107LeftParamsCertificate_eq_true :
    block107LeftParamsCertificate = true := by
  native_decide

theorem block107_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block107LeftL : ℝ) (block107LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block107S1 : ℝ))
    (hy2ne : y ≠ (block107S2 : ℝ))
    (hy3ne : y ≠ (block107S3 : ℝ))
    (hy4ne : y ≠ (block107S4 : ℝ)) :
    0 < block107V y := by
  have hcert := block107LeftCertificate_eq_true
  unfold block107LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block107LeftBoxes) (lo := block107LeftL) (hi := block107LeftR)
    (w1 := block107W1) (w2 := block107W2) (w3 := block107W3) (w4 := block107W4)
    (s1 := block107S1) (s2 := block107S2) (s3 := block107S3) (s4 := block107S4)
    hboxes hcover block107LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block107RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block107RightChunk000 block107W1 block107W2 block107W3 block107W4 block107S1 block107S2 block107S3 block107S4

theorem block107RightChunk000ParamsCertificate_eq_true :
    block107RightChunk000ParamsCertificate = true := by
  native_decide

theorem block107_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block107RightChunk000L : ℝ) (block107RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block107S1 : ℝ))
    (hy2ne : y ≠ (block107S2 : ℝ))
    (hy3ne : y ≠ (block107S3 : ℝ))
    (hy4ne : y ≠ (block107S4 : ℝ)) :
    0 < block107V y := by
  have hcert := block107RightChunk000Certificate_eq_true
  unfold block107RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block107RightChunk000) (lo := block107RightChunk000L) (hi := block107RightChunk000R)
    (w1 := block107W1) (w2 := block107W2) (w3 := block107W3) (w4 := block107W4)
    (s1 := block107S1) (s2 := block107S2) (s3 := block107S3) (s4 := block107S4)
    hboxes hcover block107RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block107_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block107RightL : ℝ) (block107RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block107S1 : ℝ))
    (hy2ne : y ≠ (block107S2 : ℝ))
    (hy3ne : y ≠ (block107S3 : ℝ))
    (hy4ne : y ≠ (block107S4 : ℝ)) :
    0 < block107V y := by
  have hL : (block107RightChunk000L : ℝ) = (block107RightL : ℝ) := by
    norm_num [block107RightChunk000L, block107RightL]
  have hR : (block107RightChunk000R : ℝ) = (block107RightR : ℝ) := by
    norm_num [block107RightChunk000R, block107RightR]
  have hyc : y ∈ Icc (block107RightChunk000L : ℝ) (block107RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block107_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block107_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block107LeftL : ℝ) (block107LeftR : ℝ) →
    y ≠ 0 → y ≠ (block107S1 : ℝ) → y ≠ (block107S2 : ℝ) →
    y ≠ (block107S3 : ℝ) → y ≠ (block107S4 : ℝ) → 0 < block107V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block107RightL : ℝ) (block107RightR : ℝ) →
    y ≠ 0 → y ≠ (block107S1 : ℝ) → y ≠ (block107S2 : ℝ) →
    y ≠ (block107S3 : ℝ) → y ≠ (block107S4 : ℝ) → 0 < block107V y)

theorem block107_reallog_certificate_proof :
    block107_reallog_certificate := by
  exact ⟨block107_left_V_pos, block107_right_V_pos⟩

end Block107
end M1817475
end Erdos1038Lean
