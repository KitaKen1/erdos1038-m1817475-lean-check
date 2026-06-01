import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block081

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block081

open Set

def block081W1 : Rat := ((3354729905910091 : Rat) / 1000000000000000)
def block081W2 : Rat := (0 : Rat)
def block081W3 : Rat := (0 : Rat)
def block081W4 : Rat := ((24095731467277443 : Rat) / 100000000000000000)
def block081S1 : Rat := ((18174751 : Rat) / 10000000)
def block081S2 : Rat := ((511587 : Rat) / 200000)
def block081S3 : Rat := ((107000619 : Rat) / 40000000)
def block081S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block081V (y : ℝ) : ℝ :=
  ratPotential block081W1 block081W2 block081W3 block081W4 block081S1 block081S2 block081S3 block081S4 y

def block081LeftParamsCertificate : Bool :=
  allBoxesSameParams block081LeftBoxes block081W1 block081W2 block081W3 block081W4 block081S1 block081S2 block081S3 block081S4

theorem block081LeftParamsCertificate_eq_true :
    block081LeftParamsCertificate = true := by
  native_decide

theorem block081_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block081LeftL : ℝ) (block081LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block081S1 : ℝ))
    (hy2ne : y ≠ (block081S2 : ℝ))
    (hy3ne : y ≠ (block081S3 : ℝ))
    (hy4ne : y ≠ (block081S4 : ℝ)) :
    0 < block081V y := by
  have hcert := block081LeftCertificate_eq_true
  unfold block081LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block081LeftBoxes) (lo := block081LeftL) (hi := block081LeftR)
    (w1 := block081W1) (w2 := block081W2) (w3 := block081W3) (w4 := block081W4)
    (s1 := block081S1) (s2 := block081S2) (s3 := block081S3) (s4 := block081S4)
    hboxes hcover block081LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block081RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block081RightChunk000 block081W1 block081W2 block081W3 block081W4 block081S1 block081S2 block081S3 block081S4

theorem block081RightChunk000ParamsCertificate_eq_true :
    block081RightChunk000ParamsCertificate = true := by
  native_decide

theorem block081_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block081RightChunk000L : ℝ) (block081RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block081S1 : ℝ))
    (hy2ne : y ≠ (block081S2 : ℝ))
    (hy3ne : y ≠ (block081S3 : ℝ))
    (hy4ne : y ≠ (block081S4 : ℝ)) :
    0 < block081V y := by
  have hcert := block081RightChunk000Certificate_eq_true
  unfold block081RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block081RightChunk000) (lo := block081RightChunk000L) (hi := block081RightChunk000R)
    (w1 := block081W1) (w2 := block081W2) (w3 := block081W3) (w4 := block081W4)
    (s1 := block081S1) (s2 := block081S2) (s3 := block081S3) (s4 := block081S4)
    hboxes hcover block081RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block081_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block081RightL : ℝ) (block081RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block081S1 : ℝ))
    (hy2ne : y ≠ (block081S2 : ℝ))
    (hy3ne : y ≠ (block081S3 : ℝ))
    (hy4ne : y ≠ (block081S4 : ℝ)) :
    0 < block081V y := by
  have hL : (block081RightChunk000L : ℝ) = (block081RightL : ℝ) := by
    norm_num [block081RightChunk000L, block081RightL]
  have hR : (block081RightChunk000R : ℝ) = (block081RightR : ℝ) := by
    norm_num [block081RightChunk000R, block081RightR]
  have hyc : y ∈ Icc (block081RightChunk000L : ℝ) (block081RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block081_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block081_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block081LeftL : ℝ) (block081LeftR : ℝ) →
    y ≠ 0 → y ≠ (block081S1 : ℝ) → y ≠ (block081S2 : ℝ) →
    y ≠ (block081S3 : ℝ) → y ≠ (block081S4 : ℝ) → 0 < block081V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block081RightL : ℝ) (block081RightR : ℝ) →
    y ≠ 0 → y ≠ (block081S1 : ℝ) → y ≠ (block081S2 : ℝ) →
    y ≠ (block081S3 : ℝ) → y ≠ (block081S4 : ℝ) → 0 < block081V y)

theorem block081_reallog_certificate_proof :
    block081_reallog_certificate := by
  exact ⟨block081_left_V_pos, block081_right_V_pos⟩

end Block081
end M1817475
end Erdos1038Lean
