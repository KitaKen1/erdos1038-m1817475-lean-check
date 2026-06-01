import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block134

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block134

open Set

def block134W1 : Rat := ((634502458472449 : Rat) / 250000000000000)
def block134W2 : Rat := (0 : Rat)
def block134W3 : Rat := ((35073040651351 : Rat) / 312500000000000)
def block134W4 : Rat := ((1284248989775097 : Rat) / 10000000000000000)
def block134S1 : Rat := ((18174751 : Rat) / 10000000)
def block134S2 : Rat := ((511587 : Rat) / 200000)
def block134S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block134S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block134V (y : ℝ) : ℝ :=
  ratPotential block134W1 block134W2 block134W3 block134W4 block134S1 block134S2 block134S3 block134S4 y

def block134LeftParamsCertificate : Bool :=
  allBoxesSameParams block134LeftBoxes block134W1 block134W2 block134W3 block134W4 block134S1 block134S2 block134S3 block134S4

theorem block134LeftParamsCertificate_eq_true :
    block134LeftParamsCertificate = true := by
  native_decide

theorem block134_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block134LeftL : ℝ) (block134LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block134S1 : ℝ))
    (hy2ne : y ≠ (block134S2 : ℝ))
    (hy3ne : y ≠ (block134S3 : ℝ))
    (hy4ne : y ≠ (block134S4 : ℝ)) :
    0 < block134V y := by
  have hcert := block134LeftCertificate_eq_true
  unfold block134LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block134LeftBoxes) (lo := block134LeftL) (hi := block134LeftR)
    (w1 := block134W1) (w2 := block134W2) (w3 := block134W3) (w4 := block134W4)
    (s1 := block134S1) (s2 := block134S2) (s3 := block134S3) (s4 := block134S4)
    hboxes hcover block134LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block134RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block134RightChunk000 block134W1 block134W2 block134W3 block134W4 block134S1 block134S2 block134S3 block134S4

theorem block134RightChunk000ParamsCertificate_eq_true :
    block134RightChunk000ParamsCertificate = true := by
  native_decide

theorem block134_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block134RightChunk000L : ℝ) (block134RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block134S1 : ℝ))
    (hy2ne : y ≠ (block134S2 : ℝ))
    (hy3ne : y ≠ (block134S3 : ℝ))
    (hy4ne : y ≠ (block134S4 : ℝ)) :
    0 < block134V y := by
  have hcert := block134RightChunk000Certificate_eq_true
  unfold block134RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block134RightChunk000) (lo := block134RightChunk000L) (hi := block134RightChunk000R)
    (w1 := block134W1) (w2 := block134W2) (w3 := block134W3) (w4 := block134W4)
    (s1 := block134S1) (s2 := block134S2) (s3 := block134S3) (s4 := block134S4)
    hboxes hcover block134RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block134_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block134RightL : ℝ) (block134RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block134S1 : ℝ))
    (hy2ne : y ≠ (block134S2 : ℝ))
    (hy3ne : y ≠ (block134S3 : ℝ))
    (hy4ne : y ≠ (block134S4 : ℝ)) :
    0 < block134V y := by
  have hL : (block134RightChunk000L : ℝ) = (block134RightL : ℝ) := by
    norm_num [block134RightChunk000L, block134RightL]
  have hR : (block134RightChunk000R : ℝ) = (block134RightR : ℝ) := by
    norm_num [block134RightChunk000R, block134RightR]
  have hyc : y ∈ Icc (block134RightChunk000L : ℝ) (block134RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block134_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block134_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block134LeftL : ℝ) (block134LeftR : ℝ) →
    y ≠ 0 → y ≠ (block134S1 : ℝ) → y ≠ (block134S2 : ℝ) →
    y ≠ (block134S3 : ℝ) → y ≠ (block134S4 : ℝ) → 0 < block134V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block134RightL : ℝ) (block134RightR : ℝ) →
    y ≠ 0 → y ≠ (block134S1 : ℝ) → y ≠ (block134S2 : ℝ) →
    y ≠ (block134S3 : ℝ) → y ≠ (block134S4 : ℝ) → 0 < block134V y)

theorem block134_reallog_certificate_proof :
    block134_reallog_certificate := by
  exact ⟨block134_left_V_pos, block134_right_V_pos⟩

end Block134
end M1817475
end Erdos1038Lean
