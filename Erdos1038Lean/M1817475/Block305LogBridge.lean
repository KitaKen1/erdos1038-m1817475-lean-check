import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block305

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block305

open Set

def block305W1 : Rat := ((2461937068237983 : Rat) / 2500000000000000)
def block305W2 : Rat := ((2095488013339159 : Rat) / 40000000000000000)
def block305W3 : Rat := ((13323557703209357 : Rat) / 50000000000000000)
def block305W4 : Rat := (0 : Rat)
def block305S1 : Rat := ((18174751 : Rat) / 10000000)
def block305S2 : Rat := ((511587 : Rat) / 200000)
def block305S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block305S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block305V (y : ℝ) : ℝ :=
  ratPotential block305W1 block305W2 block305W3 block305W4 block305S1 block305S2 block305S3 block305S4 y

def block305LeftParamsCertificate : Bool :=
  allBoxesSameParams block305LeftBoxes block305W1 block305W2 block305W3 block305W4 block305S1 block305S2 block305S3 block305S4

theorem block305LeftParamsCertificate_eq_true :
    block305LeftParamsCertificate = true := by
  native_decide

theorem block305_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block305LeftL : ℝ) (block305LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block305S1 : ℝ))
    (hy2ne : y ≠ (block305S2 : ℝ))
    (hy3ne : y ≠ (block305S3 : ℝ))
    (hy4ne : y ≠ (block305S4 : ℝ)) :
    0 < block305V y := by
  have hcert := block305LeftCertificate_eq_true
  unfold block305LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block305LeftBoxes) (lo := block305LeftL) (hi := block305LeftR)
    (w1 := block305W1) (w2 := block305W2) (w3 := block305W3) (w4 := block305W4)
    (s1 := block305S1) (s2 := block305S2) (s3 := block305S3) (s4 := block305S4)
    hboxes hcover block305LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block305RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block305RightChunk000 block305W1 block305W2 block305W3 block305W4 block305S1 block305S2 block305S3 block305S4

theorem block305RightChunk000ParamsCertificate_eq_true :
    block305RightChunk000ParamsCertificate = true := by
  native_decide

theorem block305_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block305RightChunk000L : ℝ) (block305RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block305S1 : ℝ))
    (hy2ne : y ≠ (block305S2 : ℝ))
    (hy3ne : y ≠ (block305S3 : ℝ))
    (hy4ne : y ≠ (block305S4 : ℝ)) :
    0 < block305V y := by
  have hcert := block305RightChunk000Certificate_eq_true
  unfold block305RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block305RightChunk000) (lo := block305RightChunk000L) (hi := block305RightChunk000R)
    (w1 := block305W1) (w2 := block305W2) (w3 := block305W3) (w4 := block305W4)
    (s1 := block305S1) (s2 := block305S2) (s3 := block305S3) (s4 := block305S4)
    hboxes hcover block305RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block305_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block305RightL : ℝ) (block305RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block305S1 : ℝ))
    (hy2ne : y ≠ (block305S2 : ℝ))
    (hy3ne : y ≠ (block305S3 : ℝ))
    (hy4ne : y ≠ (block305S4 : ℝ)) :
    0 < block305V y := by
  have hL : (block305RightChunk000L : ℝ) = (block305RightL : ℝ) := by
    norm_num [block305RightChunk000L, block305RightL]
  have hR : (block305RightChunk000R : ℝ) = (block305RightR : ℝ) := by
    norm_num [block305RightChunk000R, block305RightR]
  have hyc : y ∈ Icc (block305RightChunk000L : ℝ) (block305RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block305_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block305_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block305LeftL : ℝ) (block305LeftR : ℝ) →
    y ≠ 0 → y ≠ (block305S1 : ℝ) → y ≠ (block305S2 : ℝ) →
    y ≠ (block305S3 : ℝ) → y ≠ (block305S4 : ℝ) → 0 < block305V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block305RightL : ℝ) (block305RightR : ℝ) →
    y ≠ 0 → y ≠ (block305S1 : ℝ) → y ≠ (block305S2 : ℝ) →
    y ≠ (block305S3 : ℝ) → y ≠ (block305S4 : ℝ) → 0 < block305V y)

theorem block305_reallog_certificate_proof :
    block305_reallog_certificate := by
  exact ⟨block305_left_V_pos, block305_right_V_pos⟩

end Block305
end M1817475
end Erdos1038Lean
