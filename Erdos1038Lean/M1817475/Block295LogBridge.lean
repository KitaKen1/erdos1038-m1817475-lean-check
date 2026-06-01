import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block295

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block295

open Set

def block295W1 : Rat := ((10130819832772469 : Rat) / 10000000000000000)
def block295W2 : Rat := ((2130077931851337 : Rat) / 50000000000000000)
def block295W3 : Rat := ((27532409392564927 : Rat) / 100000000000000000)
def block295W4 : Rat := (0 : Rat)
def block295S1 : Rat := ((18174751 : Rat) / 10000000)
def block295S2 : Rat := ((511587 : Rat) / 200000)
def block295S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block295S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block295V (y : ℝ) : ℝ :=
  ratPotential block295W1 block295W2 block295W3 block295W4 block295S1 block295S2 block295S3 block295S4 y

def block295LeftParamsCertificate : Bool :=
  allBoxesSameParams block295LeftBoxes block295W1 block295W2 block295W3 block295W4 block295S1 block295S2 block295S3 block295S4

theorem block295LeftParamsCertificate_eq_true :
    block295LeftParamsCertificate = true := by
  native_decide

theorem block295_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block295LeftL : ℝ) (block295LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block295S1 : ℝ))
    (hy2ne : y ≠ (block295S2 : ℝ))
    (hy3ne : y ≠ (block295S3 : ℝ))
    (hy4ne : y ≠ (block295S4 : ℝ)) :
    0 < block295V y := by
  have hcert := block295LeftCertificate_eq_true
  unfold block295LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block295LeftBoxes) (lo := block295LeftL) (hi := block295LeftR)
    (w1 := block295W1) (w2 := block295W2) (w3 := block295W3) (w4 := block295W4)
    (s1 := block295S1) (s2 := block295S2) (s3 := block295S3) (s4 := block295S4)
    hboxes hcover block295LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block295RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block295RightChunk000 block295W1 block295W2 block295W3 block295W4 block295S1 block295S2 block295S3 block295S4

theorem block295RightChunk000ParamsCertificate_eq_true :
    block295RightChunk000ParamsCertificate = true := by
  native_decide

theorem block295_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block295RightChunk000L : ℝ) (block295RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block295S1 : ℝ))
    (hy2ne : y ≠ (block295S2 : ℝ))
    (hy3ne : y ≠ (block295S3 : ℝ))
    (hy4ne : y ≠ (block295S4 : ℝ)) :
    0 < block295V y := by
  have hcert := block295RightChunk000Certificate_eq_true
  unfold block295RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block295RightChunk000) (lo := block295RightChunk000L) (hi := block295RightChunk000R)
    (w1 := block295W1) (w2 := block295W2) (w3 := block295W3) (w4 := block295W4)
    (s1 := block295S1) (s2 := block295S2) (s3 := block295S3) (s4 := block295S4)
    hboxes hcover block295RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block295_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block295RightL : ℝ) (block295RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block295S1 : ℝ))
    (hy2ne : y ≠ (block295S2 : ℝ))
    (hy3ne : y ≠ (block295S3 : ℝ))
    (hy4ne : y ≠ (block295S4 : ℝ)) :
    0 < block295V y := by
  have hL : (block295RightChunk000L : ℝ) = (block295RightL : ℝ) := by
    norm_num [block295RightChunk000L, block295RightL]
  have hR : (block295RightChunk000R : ℝ) = (block295RightR : ℝ) := by
    norm_num [block295RightChunk000R, block295RightR]
  have hyc : y ∈ Icc (block295RightChunk000L : ℝ) (block295RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block295_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block295_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block295LeftL : ℝ) (block295LeftR : ℝ) →
    y ≠ 0 → y ≠ (block295S1 : ℝ) → y ≠ (block295S2 : ℝ) →
    y ≠ (block295S3 : ℝ) → y ≠ (block295S4 : ℝ) → 0 < block295V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block295RightL : ℝ) (block295RightR : ℝ) →
    y ≠ 0 → y ≠ (block295S1 : ℝ) → y ≠ (block295S2 : ℝ) →
    y ≠ (block295S3 : ℝ) → y ≠ (block295S4 : ℝ) → 0 < block295V y)

theorem block295_reallog_certificate_proof :
    block295_reallog_certificate := by
  exact ⟨block295_left_V_pos, block295_right_V_pos⟩

end Block295
end M1817475
end Erdos1038Lean
