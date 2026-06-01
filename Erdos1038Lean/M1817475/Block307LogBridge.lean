import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block307

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block307

open Set

def block307W1 : Rat := ((1958084359383149 : Rat) / 2000000000000000)
def block307W2 : Rat := ((5442837380131751 : Rat) / 100000000000000000)
def block307W3 : Rat := ((2646629312862137 : Rat) / 10000000000000000)
def block307W4 : Rat := (0 : Rat)
def block307S1 : Rat := ((18174751 : Rat) / 10000000)
def block307S2 : Rat := ((511587 : Rat) / 200000)
def block307S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block307S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block307V (y : ℝ) : ℝ :=
  ratPotential block307W1 block307W2 block307W3 block307W4 block307S1 block307S2 block307S3 block307S4 y

def block307LeftParamsCertificate : Bool :=
  allBoxesSameParams block307LeftBoxes block307W1 block307W2 block307W3 block307W4 block307S1 block307S2 block307S3 block307S4

theorem block307LeftParamsCertificate_eq_true :
    block307LeftParamsCertificate = true := by
  native_decide

theorem block307_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block307LeftL : ℝ) (block307LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block307S1 : ℝ))
    (hy2ne : y ≠ (block307S2 : ℝ))
    (hy3ne : y ≠ (block307S3 : ℝ))
    (hy4ne : y ≠ (block307S4 : ℝ)) :
    0 < block307V y := by
  have hcert := block307LeftCertificate_eq_true
  unfold block307LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block307LeftBoxes) (lo := block307LeftL) (hi := block307LeftR)
    (w1 := block307W1) (w2 := block307W2) (w3 := block307W3) (w4 := block307W4)
    (s1 := block307S1) (s2 := block307S2) (s3 := block307S3) (s4 := block307S4)
    hboxes hcover block307LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block307RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block307RightChunk000 block307W1 block307W2 block307W3 block307W4 block307S1 block307S2 block307S3 block307S4

theorem block307RightChunk000ParamsCertificate_eq_true :
    block307RightChunk000ParamsCertificate = true := by
  native_decide

theorem block307_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block307RightChunk000L : ℝ) (block307RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block307S1 : ℝ))
    (hy2ne : y ≠ (block307S2 : ℝ))
    (hy3ne : y ≠ (block307S3 : ℝ))
    (hy4ne : y ≠ (block307S4 : ℝ)) :
    0 < block307V y := by
  have hcert := block307RightChunk000Certificate_eq_true
  unfold block307RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block307RightChunk000) (lo := block307RightChunk000L) (hi := block307RightChunk000R)
    (w1 := block307W1) (w2 := block307W2) (w3 := block307W3) (w4 := block307W4)
    (s1 := block307S1) (s2 := block307S2) (s3 := block307S3) (s4 := block307S4)
    hboxes hcover block307RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block307_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block307RightL : ℝ) (block307RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block307S1 : ℝ))
    (hy2ne : y ≠ (block307S2 : ℝ))
    (hy3ne : y ≠ (block307S3 : ℝ))
    (hy4ne : y ≠ (block307S4 : ℝ)) :
    0 < block307V y := by
  have hL : (block307RightChunk000L : ℝ) = (block307RightL : ℝ) := by
    norm_num [block307RightChunk000L, block307RightL]
  have hR : (block307RightChunk000R : ℝ) = (block307RightR : ℝ) := by
    norm_num [block307RightChunk000R, block307RightR]
  have hyc : y ∈ Icc (block307RightChunk000L : ℝ) (block307RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block307_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block307_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block307LeftL : ℝ) (block307LeftR : ℝ) →
    y ≠ 0 → y ≠ (block307S1 : ℝ) → y ≠ (block307S2 : ℝ) →
    y ≠ (block307S3 : ℝ) → y ≠ (block307S4 : ℝ) → 0 < block307V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block307RightL : ℝ) (block307RightR : ℝ) →
    y ≠ 0 → y ≠ (block307S1 : ℝ) → y ≠ (block307S2 : ℝ) →
    y ≠ (block307S3 : ℝ) → y ≠ (block307S4 : ℝ) → 0 < block307V y)

theorem block307_reallog_certificate_proof :
    block307_reallog_certificate := by
  exact ⟨block307_left_V_pos, block307_right_V_pos⟩

end Block307
end M1817475
end Erdos1038Lean
