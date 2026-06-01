import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block106

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block106

open Set

def block106W1 : Rat := ((6471665979041603 : Rat) / 2500000000000000)
def block106W2 : Rat := (0 : Rat)
def block106W3 : Rat := ((28427595181116913 : Rat) / 500000000000000000)
def block106W4 : Rat := ((9474955664217967 : Rat) / 50000000000000000)
def block106S1 : Rat := ((18174751 : Rat) / 10000000)
def block106S2 : Rat := ((511587 : Rat) / 200000)
def block106S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block106S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block106V (y : ℝ) : ℝ :=
  ratPotential block106W1 block106W2 block106W3 block106W4 block106S1 block106S2 block106S3 block106S4 y

def block106LeftParamsCertificate : Bool :=
  allBoxesSameParams block106LeftBoxes block106W1 block106W2 block106W3 block106W4 block106S1 block106S2 block106S3 block106S4

theorem block106LeftParamsCertificate_eq_true :
    block106LeftParamsCertificate = true := by
  native_decide

theorem block106_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block106LeftL : ℝ) (block106LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block106S1 : ℝ))
    (hy2ne : y ≠ (block106S2 : ℝ))
    (hy3ne : y ≠ (block106S3 : ℝ))
    (hy4ne : y ≠ (block106S4 : ℝ)) :
    0 < block106V y := by
  have hcert := block106LeftCertificate_eq_true
  unfold block106LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block106LeftBoxes) (lo := block106LeftL) (hi := block106LeftR)
    (w1 := block106W1) (w2 := block106W2) (w3 := block106W3) (w4 := block106W4)
    (s1 := block106S1) (s2 := block106S2) (s3 := block106S3) (s4 := block106S4)
    hboxes hcover block106LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block106RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block106RightChunk000 block106W1 block106W2 block106W3 block106W4 block106S1 block106S2 block106S3 block106S4

theorem block106RightChunk000ParamsCertificate_eq_true :
    block106RightChunk000ParamsCertificate = true := by
  native_decide

theorem block106_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block106RightChunk000L : ℝ) (block106RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block106S1 : ℝ))
    (hy2ne : y ≠ (block106S2 : ℝ))
    (hy3ne : y ≠ (block106S3 : ℝ))
    (hy4ne : y ≠ (block106S4 : ℝ)) :
    0 < block106V y := by
  have hcert := block106RightChunk000Certificate_eq_true
  unfold block106RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block106RightChunk000) (lo := block106RightChunk000L) (hi := block106RightChunk000R)
    (w1 := block106W1) (w2 := block106W2) (w3 := block106W3) (w4 := block106W4)
    (s1 := block106S1) (s2 := block106S2) (s3 := block106S3) (s4 := block106S4)
    hboxes hcover block106RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block106_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block106RightL : ℝ) (block106RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block106S1 : ℝ))
    (hy2ne : y ≠ (block106S2 : ℝ))
    (hy3ne : y ≠ (block106S3 : ℝ))
    (hy4ne : y ≠ (block106S4 : ℝ)) :
    0 < block106V y := by
  have hL : (block106RightChunk000L : ℝ) = (block106RightL : ℝ) := by
    norm_num [block106RightChunk000L, block106RightL]
  have hR : (block106RightChunk000R : ℝ) = (block106RightR : ℝ) := by
    norm_num [block106RightChunk000R, block106RightR]
  have hyc : y ∈ Icc (block106RightChunk000L : ℝ) (block106RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block106_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block106_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block106LeftL : ℝ) (block106LeftR : ℝ) →
    y ≠ 0 → y ≠ (block106S1 : ℝ) → y ≠ (block106S2 : ℝ) →
    y ≠ (block106S3 : ℝ) → y ≠ (block106S4 : ℝ) → 0 < block106V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block106RightL : ℝ) (block106RightR : ℝ) →
    y ≠ 0 → y ≠ (block106S1 : ℝ) → y ≠ (block106S2 : ℝ) →
    y ≠ (block106S3 : ℝ) → y ≠ (block106S4 : ℝ) → 0 < block106V y)

theorem block106_reallog_certificate_proof :
    block106_reallog_certificate := by
  exact ⟨block106_left_V_pos, block106_right_V_pos⟩

end Block106
end M1817475
end Erdos1038Lean
