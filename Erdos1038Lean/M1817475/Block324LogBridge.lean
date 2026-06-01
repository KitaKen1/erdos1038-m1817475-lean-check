import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block324

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block324

open Set

def block324W1 : Rat := ((185870090717119 : Rat) / 200000000000000)
def block324W2 : Rat := ((3647310943711163 : Rat) / 50000000000000000)
def block324W3 : Rat := ((24877801809365657 : Rat) / 100000000000000000)
def block324W4 : Rat := (0 : Rat)
def block324S1 : Rat := ((18174751 : Rat) / 10000000)
def block324S2 : Rat := ((511587 : Rat) / 200000)
def block324S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block324S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block324V (y : ℝ) : ℝ :=
  ratPotential block324W1 block324W2 block324W3 block324W4 block324S1 block324S2 block324S3 block324S4 y

def block324LeftParamsCertificate : Bool :=
  allBoxesSameParams block324LeftBoxes block324W1 block324W2 block324W3 block324W4 block324S1 block324S2 block324S3 block324S4

theorem block324LeftParamsCertificate_eq_true :
    block324LeftParamsCertificate = true := by
  native_decide

theorem block324_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block324LeftL : ℝ) (block324LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block324S1 : ℝ))
    (hy2ne : y ≠ (block324S2 : ℝ))
    (hy3ne : y ≠ (block324S3 : ℝ))
    (hy4ne : y ≠ (block324S4 : ℝ)) :
    0 < block324V y := by
  have hcert := block324LeftCertificate_eq_true
  unfold block324LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block324LeftBoxes) (lo := block324LeftL) (hi := block324LeftR)
    (w1 := block324W1) (w2 := block324W2) (w3 := block324W3) (w4 := block324W4)
    (s1 := block324S1) (s2 := block324S2) (s3 := block324S3) (s4 := block324S4)
    hboxes hcover block324LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block324RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block324RightChunk000 block324W1 block324W2 block324W3 block324W4 block324S1 block324S2 block324S3 block324S4

theorem block324RightChunk000ParamsCertificate_eq_true :
    block324RightChunk000ParamsCertificate = true := by
  native_decide

theorem block324_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block324RightChunk000L : ℝ) (block324RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block324S1 : ℝ))
    (hy2ne : y ≠ (block324S2 : ℝ))
    (hy3ne : y ≠ (block324S3 : ℝ))
    (hy4ne : y ≠ (block324S4 : ℝ)) :
    0 < block324V y := by
  have hcert := block324RightChunk000Certificate_eq_true
  unfold block324RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block324RightChunk000) (lo := block324RightChunk000L) (hi := block324RightChunk000R)
    (w1 := block324W1) (w2 := block324W2) (w3 := block324W3) (w4 := block324W4)
    (s1 := block324S1) (s2 := block324S2) (s3 := block324S3) (s4 := block324S4)
    hboxes hcover block324RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block324_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block324RightL : ℝ) (block324RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block324S1 : ℝ))
    (hy2ne : y ≠ (block324S2 : ℝ))
    (hy3ne : y ≠ (block324S3 : ℝ))
    (hy4ne : y ≠ (block324S4 : ℝ)) :
    0 < block324V y := by
  have hL : (block324RightChunk000L : ℝ) = (block324RightL : ℝ) := by
    norm_num [block324RightChunk000L, block324RightL]
  have hR : (block324RightChunk000R : ℝ) = (block324RightR : ℝ) := by
    norm_num [block324RightChunk000R, block324RightR]
  have hyc : y ∈ Icc (block324RightChunk000L : ℝ) (block324RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block324_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block324_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block324LeftL : ℝ) (block324LeftR : ℝ) →
    y ≠ 0 → y ≠ (block324S1 : ℝ) → y ≠ (block324S2 : ℝ) →
    y ≠ (block324S3 : ℝ) → y ≠ (block324S4 : ℝ) → 0 < block324V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block324RightL : ℝ) (block324RightR : ℝ) →
    y ≠ 0 → y ≠ (block324S1 : ℝ) → y ≠ (block324S2 : ℝ) →
    y ≠ (block324S3 : ℝ) → y ≠ (block324S4 : ℝ) → 0 < block324V y)

theorem block324_reallog_certificate_proof :
    block324_reallog_certificate := by
  exact ⟨block324_left_V_pos, block324_right_V_pos⟩

end Block324
end M1817475
end Erdos1038Lean
