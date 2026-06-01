import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block097

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block097

open Set

def block097W1 : Rat := ((2628292425036879 : Rat) / 1000000000000000)
def block097W2 : Rat := (0 : Rat)
def block097W3 : Rat := ((1128636878625561 : Rat) / 25000000000000000)
def block097W4 : Rat := ((10187091198326591 : Rat) / 50000000000000000)
def block097S1 : Rat := ((18174751 : Rat) / 10000000)
def block097S2 : Rat := ((511587 : Rat) / 200000)
def block097S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block097S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block097V (y : ℝ) : ℝ :=
  ratPotential block097W1 block097W2 block097W3 block097W4 block097S1 block097S2 block097S3 block097S4 y

def block097LeftParamsCertificate : Bool :=
  allBoxesSameParams block097LeftBoxes block097W1 block097W2 block097W3 block097W4 block097S1 block097S2 block097S3 block097S4

theorem block097LeftParamsCertificate_eq_true :
    block097LeftParamsCertificate = true := by
  native_decide

theorem block097_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block097LeftL : ℝ) (block097LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block097S1 : ℝ))
    (hy2ne : y ≠ (block097S2 : ℝ))
    (hy3ne : y ≠ (block097S3 : ℝ))
    (hy4ne : y ≠ (block097S4 : ℝ)) :
    0 < block097V y := by
  have hcert := block097LeftCertificate_eq_true
  unfold block097LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block097LeftBoxes) (lo := block097LeftL) (hi := block097LeftR)
    (w1 := block097W1) (w2 := block097W2) (w3 := block097W3) (w4 := block097W4)
    (s1 := block097S1) (s2 := block097S2) (s3 := block097S3) (s4 := block097S4)
    hboxes hcover block097LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block097RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block097RightChunk000 block097W1 block097W2 block097W3 block097W4 block097S1 block097S2 block097S3 block097S4

theorem block097RightChunk000ParamsCertificate_eq_true :
    block097RightChunk000ParamsCertificate = true := by
  native_decide

theorem block097_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block097RightChunk000L : ℝ) (block097RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block097S1 : ℝ))
    (hy2ne : y ≠ (block097S2 : ℝ))
    (hy3ne : y ≠ (block097S3 : ℝ))
    (hy4ne : y ≠ (block097S4 : ℝ)) :
    0 < block097V y := by
  have hcert := block097RightChunk000Certificate_eq_true
  unfold block097RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block097RightChunk000) (lo := block097RightChunk000L) (hi := block097RightChunk000R)
    (w1 := block097W1) (w2 := block097W2) (w3 := block097W3) (w4 := block097W4)
    (s1 := block097S1) (s2 := block097S2) (s3 := block097S3) (s4 := block097S4)
    hboxes hcover block097RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block097_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block097RightL : ℝ) (block097RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block097S1 : ℝ))
    (hy2ne : y ≠ (block097S2 : ℝ))
    (hy3ne : y ≠ (block097S3 : ℝ))
    (hy4ne : y ≠ (block097S4 : ℝ)) :
    0 < block097V y := by
  have hL : (block097RightChunk000L : ℝ) = (block097RightL : ℝ) := by
    norm_num [block097RightChunk000L, block097RightL]
  have hR : (block097RightChunk000R : ℝ) = (block097RightR : ℝ) := by
    norm_num [block097RightChunk000R, block097RightR]
  have hyc : y ∈ Icc (block097RightChunk000L : ℝ) (block097RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block097_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block097_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block097LeftL : ℝ) (block097LeftR : ℝ) →
    y ≠ 0 → y ≠ (block097S1 : ℝ) → y ≠ (block097S2 : ℝ) →
    y ≠ (block097S3 : ℝ) → y ≠ (block097S4 : ℝ) → 0 < block097V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block097RightL : ℝ) (block097RightR : ℝ) →
    y ≠ 0 → y ≠ (block097S1 : ℝ) → y ≠ (block097S2 : ℝ) →
    y ≠ (block097S3 : ℝ) → y ≠ (block097S4 : ℝ) → 0 < block097V y)

theorem block097_reallog_certificate_proof :
    block097_reallog_certificate := by
  exact ⟨block097_left_V_pos, block097_right_V_pos⟩

end Block097
end M1817475
end Erdos1038Lean
