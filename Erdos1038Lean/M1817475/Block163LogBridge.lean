import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block163

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block163

open Set

def block163W1 : Rat := ((2312780852058681 : Rat) / 1250000000000000)
def block163W2 : Rat := (0 : Rat)
def block163W3 : Rat := ((1633680591457383 : Rat) / 10000000000000000)
def block163W4 : Rat := ((10431899445997611 : Rat) / 100000000000000000)
def block163S1 : Rat := ((18174751 : Rat) / 10000000)
def block163S2 : Rat := ((511587 : Rat) / 200000)
def block163S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block163S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block163V (y : ℝ) : ℝ :=
  ratPotential block163W1 block163W2 block163W3 block163W4 block163S1 block163S2 block163S3 block163S4 y

def block163LeftParamsCertificate : Bool :=
  allBoxesSameParams block163LeftBoxes block163W1 block163W2 block163W3 block163W4 block163S1 block163S2 block163S3 block163S4

theorem block163LeftParamsCertificate_eq_true :
    block163LeftParamsCertificate = true := by
  native_decide

theorem block163_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block163LeftL : ℝ) (block163LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block163S1 : ℝ))
    (hy2ne : y ≠ (block163S2 : ℝ))
    (hy3ne : y ≠ (block163S3 : ℝ))
    (hy4ne : y ≠ (block163S4 : ℝ)) :
    0 < block163V y := by
  have hcert := block163LeftCertificate_eq_true
  unfold block163LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block163LeftBoxes) (lo := block163LeftL) (hi := block163LeftR)
    (w1 := block163W1) (w2 := block163W2) (w3 := block163W3) (w4 := block163W4)
    (s1 := block163S1) (s2 := block163S2) (s3 := block163S3) (s4 := block163S4)
    hboxes hcover block163LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block163RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block163RightChunk000 block163W1 block163W2 block163W3 block163W4 block163S1 block163S2 block163S3 block163S4

theorem block163RightChunk000ParamsCertificate_eq_true :
    block163RightChunk000ParamsCertificate = true := by
  native_decide

theorem block163_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block163RightChunk000L : ℝ) (block163RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block163S1 : ℝ))
    (hy2ne : y ≠ (block163S2 : ℝ))
    (hy3ne : y ≠ (block163S3 : ℝ))
    (hy4ne : y ≠ (block163S4 : ℝ)) :
    0 < block163V y := by
  have hcert := block163RightChunk000Certificate_eq_true
  unfold block163RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block163RightChunk000) (lo := block163RightChunk000L) (hi := block163RightChunk000R)
    (w1 := block163W1) (w2 := block163W2) (w3 := block163W3) (w4 := block163W4)
    (s1 := block163S1) (s2 := block163S2) (s3 := block163S3) (s4 := block163S4)
    hboxes hcover block163RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block163_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block163RightL : ℝ) (block163RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block163S1 : ℝ))
    (hy2ne : y ≠ (block163S2 : ℝ))
    (hy3ne : y ≠ (block163S3 : ℝ))
    (hy4ne : y ≠ (block163S4 : ℝ)) :
    0 < block163V y := by
  have hL : (block163RightChunk000L : ℝ) = (block163RightL : ℝ) := by
    norm_num [block163RightChunk000L, block163RightL]
  have hR : (block163RightChunk000R : ℝ) = (block163RightR : ℝ) := by
    norm_num [block163RightChunk000R, block163RightR]
  have hyc : y ∈ Icc (block163RightChunk000L : ℝ) (block163RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block163_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block163_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block163LeftL : ℝ) (block163LeftR : ℝ) →
    y ≠ 0 → y ≠ (block163S1 : ℝ) → y ≠ (block163S2 : ℝ) →
    y ≠ (block163S3 : ℝ) → y ≠ (block163S4 : ℝ) → 0 < block163V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block163RightL : ℝ) (block163RightR : ℝ) →
    y ≠ 0 → y ≠ (block163S1 : ℝ) → y ≠ (block163S2 : ℝ) →
    y ≠ (block163S3 : ℝ) → y ≠ (block163S4 : ℝ) → 0 < block163V y)

theorem block163_reallog_certificate_proof :
    block163_reallog_certificate := by
  exact ⟨block163_left_V_pos, block163_right_V_pos⟩

end Block163
end M1817475
end Erdos1038Lean
