import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block315

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block315

open Set

def block315W1 : Rat := ((1194842248261797 : Rat) / 1250000000000000)
def block315W2 : Rat := ((6287883829412763 : Rat) / 100000000000000000)
def block315W3 : Rat := ((402036607648991 : Rat) / 1562500000000000)
def block315W4 : Rat := (0 : Rat)
def block315S1 : Rat := ((18174751 : Rat) / 10000000)
def block315S2 : Rat := ((511587 : Rat) / 200000)
def block315S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block315S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block315V (y : ℝ) : ℝ :=
  ratPotential block315W1 block315W2 block315W3 block315W4 block315S1 block315S2 block315S3 block315S4 y

def block315LeftParamsCertificate : Bool :=
  allBoxesSameParams block315LeftBoxes block315W1 block315W2 block315W3 block315W4 block315S1 block315S2 block315S3 block315S4

theorem block315LeftParamsCertificate_eq_true :
    block315LeftParamsCertificate = true := by
  native_decide

theorem block315_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block315LeftL : ℝ) (block315LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block315S1 : ℝ))
    (hy2ne : y ≠ (block315S2 : ℝ))
    (hy3ne : y ≠ (block315S3 : ℝ))
    (hy4ne : y ≠ (block315S4 : ℝ)) :
    0 < block315V y := by
  have hcert := block315LeftCertificate_eq_true
  unfold block315LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block315LeftBoxes) (lo := block315LeftL) (hi := block315LeftR)
    (w1 := block315W1) (w2 := block315W2) (w3 := block315W3) (w4 := block315W4)
    (s1 := block315S1) (s2 := block315S2) (s3 := block315S3) (s4 := block315S4)
    hboxes hcover block315LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block315RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block315RightChunk000 block315W1 block315W2 block315W3 block315W4 block315S1 block315S2 block315S3 block315S4

theorem block315RightChunk000ParamsCertificate_eq_true :
    block315RightChunk000ParamsCertificate = true := by
  native_decide

theorem block315_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block315RightChunk000L : ℝ) (block315RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block315S1 : ℝ))
    (hy2ne : y ≠ (block315S2 : ℝ))
    (hy3ne : y ≠ (block315S3 : ℝ))
    (hy4ne : y ≠ (block315S4 : ℝ)) :
    0 < block315V y := by
  have hcert := block315RightChunk000Certificate_eq_true
  unfold block315RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block315RightChunk000) (lo := block315RightChunk000L) (hi := block315RightChunk000R)
    (w1 := block315W1) (w2 := block315W2) (w3 := block315W3) (w4 := block315W4)
    (s1 := block315S1) (s2 := block315S2) (s3 := block315S3) (s4 := block315S4)
    hboxes hcover block315RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block315_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block315RightL : ℝ) (block315RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block315S1 : ℝ))
    (hy2ne : y ≠ (block315S2 : ℝ))
    (hy3ne : y ≠ (block315S3 : ℝ))
    (hy4ne : y ≠ (block315S4 : ℝ)) :
    0 < block315V y := by
  have hL : (block315RightChunk000L : ℝ) = (block315RightL : ℝ) := by
    norm_num [block315RightChunk000L, block315RightL]
  have hR : (block315RightChunk000R : ℝ) = (block315RightR : ℝ) := by
    norm_num [block315RightChunk000R, block315RightR]
  have hyc : y ∈ Icc (block315RightChunk000L : ℝ) (block315RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block315_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block315_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block315LeftL : ℝ) (block315LeftR : ℝ) →
    y ≠ 0 → y ≠ (block315S1 : ℝ) → y ≠ (block315S2 : ℝ) →
    y ≠ (block315S3 : ℝ) → y ≠ (block315S4 : ℝ) → 0 < block315V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block315RightL : ℝ) (block315RightR : ℝ) →
    y ≠ 0 → y ≠ (block315S1 : ℝ) → y ≠ (block315S2 : ℝ) →
    y ≠ (block315S3 : ℝ) → y ≠ (block315S4 : ℝ) → 0 < block315V y)

theorem block315_reallog_certificate_proof :
    block315_reallog_certificate := by
  exact ⟨block315_left_V_pos, block315_right_V_pos⟩

end Block315
end M1817475
end Erdos1038Lean
