import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block292

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block292

open Set

def block292W1 : Rat := ((10214579730994233 : Rat) / 10000000000000000)
def block292W2 : Rat := ((995026954894167 : Rat) / 25000000000000000)
def block292W3 : Rat := ((5558378298072043 : Rat) / 20000000000000000)
def block292W4 : Rat := (0 : Rat)
def block292S1 : Rat := ((18174751 : Rat) / 10000000)
def block292S2 : Rat := ((511587 : Rat) / 200000)
def block292S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block292S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block292V (y : ℝ) : ℝ :=
  ratPotential block292W1 block292W2 block292W3 block292W4 block292S1 block292S2 block292S3 block292S4 y

def block292LeftParamsCertificate : Bool :=
  allBoxesSameParams block292LeftBoxes block292W1 block292W2 block292W3 block292W4 block292S1 block292S2 block292S3 block292S4

theorem block292LeftParamsCertificate_eq_true :
    block292LeftParamsCertificate = true := by
  native_decide

theorem block292_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block292LeftL : ℝ) (block292LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block292S1 : ℝ))
    (hy2ne : y ≠ (block292S2 : ℝ))
    (hy3ne : y ≠ (block292S3 : ℝ))
    (hy4ne : y ≠ (block292S4 : ℝ)) :
    0 < block292V y := by
  have hcert := block292LeftCertificate_eq_true
  unfold block292LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block292LeftBoxes) (lo := block292LeftL) (hi := block292LeftR)
    (w1 := block292W1) (w2 := block292W2) (w3 := block292W3) (w4 := block292W4)
    (s1 := block292S1) (s2 := block292S2) (s3 := block292S3) (s4 := block292S4)
    hboxes hcover block292LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block292RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block292RightChunk000 block292W1 block292W2 block292W3 block292W4 block292S1 block292S2 block292S3 block292S4

theorem block292RightChunk000ParamsCertificate_eq_true :
    block292RightChunk000ParamsCertificate = true := by
  native_decide

theorem block292_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block292RightChunk000L : ℝ) (block292RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block292S1 : ℝ))
    (hy2ne : y ≠ (block292S2 : ℝ))
    (hy3ne : y ≠ (block292S3 : ℝ))
    (hy4ne : y ≠ (block292S4 : ℝ)) :
    0 < block292V y := by
  have hcert := block292RightChunk000Certificate_eq_true
  unfold block292RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block292RightChunk000) (lo := block292RightChunk000L) (hi := block292RightChunk000R)
    (w1 := block292W1) (w2 := block292W2) (w3 := block292W3) (w4 := block292W4)
    (s1 := block292S1) (s2 := block292S2) (s3 := block292S3) (s4 := block292S4)
    hboxes hcover block292RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block292_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block292RightL : ℝ) (block292RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block292S1 : ℝ))
    (hy2ne : y ≠ (block292S2 : ℝ))
    (hy3ne : y ≠ (block292S3 : ℝ))
    (hy4ne : y ≠ (block292S4 : ℝ)) :
    0 < block292V y := by
  have hL : (block292RightChunk000L : ℝ) = (block292RightL : ℝ) := by
    norm_num [block292RightChunk000L, block292RightL]
  have hR : (block292RightChunk000R : ℝ) = (block292RightR : ℝ) := by
    norm_num [block292RightChunk000R, block292RightR]
  have hyc : y ∈ Icc (block292RightChunk000L : ℝ) (block292RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block292_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block292_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block292LeftL : ℝ) (block292LeftR : ℝ) →
    y ≠ 0 → y ≠ (block292S1 : ℝ) → y ≠ (block292S2 : ℝ) →
    y ≠ (block292S3 : ℝ) → y ≠ (block292S4 : ℝ) → 0 < block292V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block292RightL : ℝ) (block292RightR : ℝ) →
    y ≠ 0 → y ≠ (block292S1 : ℝ) → y ≠ (block292S2 : ℝ) →
    y ≠ (block292S3 : ℝ) → y ≠ (block292S4 : ℝ) → 0 < block292V y)

theorem block292_reallog_certificate_proof :
    block292_reallog_certificate := by
  exact ⟨block292_left_V_pos, block292_right_V_pos⟩

end Block292
end M1817475
end Erdos1038Lean
