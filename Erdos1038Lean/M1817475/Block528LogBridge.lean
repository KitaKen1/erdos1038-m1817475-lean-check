import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block528

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block528

open Set

def block528W1 : Rat := ((40989925788787807 : Rat) / 100000000000000000)
def block528W2 : Rat := (0 : Rat)
def block528W3 : Rat := ((5642927911012563 : Rat) / 12500000000000000)
def block528W4 : Rat := (0 : Rat)
def block528S1 : Rat := ((18174751 : Rat) / 10000000)
def block528S2 : Rat := ((511587 : Rat) / 200000)
def block528S3 : Rat := ((129811628660714285887 : Rat) / 50000000000000000000)
def block528S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block528V (y : ℝ) : ℝ :=
  ratPotential block528W1 block528W2 block528W3 block528W4 block528S1 block528S2 block528S3 block528S4 y

def block528LeftParamsCertificate : Bool :=
  allBoxesSameParams block528LeftBoxes block528W1 block528W2 block528W3 block528W4 block528S1 block528S2 block528S3 block528S4

theorem block528LeftParamsCertificate_eq_true :
    block528LeftParamsCertificate = true := by
  native_decide

theorem block528_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block528LeftL : ℝ) (block528LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block528S1 : ℝ))
    (hy2ne : y ≠ (block528S2 : ℝ))
    (hy3ne : y ≠ (block528S3 : ℝ))
    (hy4ne : y ≠ (block528S4 : ℝ)) :
    0 < block528V y := by
  have hcert := block528LeftCertificate_eq_true
  unfold block528LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block528LeftBoxes) (lo := block528LeftL) (hi := block528LeftR)
    (w1 := block528W1) (w2 := block528W2) (w3 := block528W3) (w4 := block528W4)
    (s1 := block528S1) (s2 := block528S2) (s3 := block528S3) (s4 := block528S4)
    hboxes hcover block528LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block528RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block528RightChunk000 block528W1 block528W2 block528W3 block528W4 block528S1 block528S2 block528S3 block528S4

theorem block528RightChunk000ParamsCertificate_eq_true :
    block528RightChunk000ParamsCertificate = true := by
  native_decide

theorem block528_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block528RightChunk000L : ℝ) (block528RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block528S1 : ℝ))
    (hy2ne : y ≠ (block528S2 : ℝ))
    (hy3ne : y ≠ (block528S3 : ℝ))
    (hy4ne : y ≠ (block528S4 : ℝ)) :
    0 < block528V y := by
  have hcert := block528RightChunk000Certificate_eq_true
  unfold block528RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block528RightChunk000) (lo := block528RightChunk000L) (hi := block528RightChunk000R)
    (w1 := block528W1) (w2 := block528W2) (w3 := block528W3) (w4 := block528W4)
    (s1 := block528S1) (s2 := block528S2) (s3 := block528S3) (s4 := block528S4)
    hboxes hcover block528RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block528_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block528RightL : ℝ) (block528RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block528S1 : ℝ))
    (hy2ne : y ≠ (block528S2 : ℝ))
    (hy3ne : y ≠ (block528S3 : ℝ))
    (hy4ne : y ≠ (block528S4 : ℝ)) :
    0 < block528V y := by
  have hL : (block528RightChunk000L : ℝ) = (block528RightL : ℝ) := by
    norm_num [block528RightChunk000L, block528RightL]
  have hR : (block528RightChunk000R : ℝ) = (block528RightR : ℝ) := by
    norm_num [block528RightChunk000R, block528RightR]
  have hyc : y ∈ Icc (block528RightChunk000L : ℝ) (block528RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block528_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block528_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block528LeftL : ℝ) (block528LeftR : ℝ) →
    y ≠ 0 → y ≠ (block528S1 : ℝ) → y ≠ (block528S2 : ℝ) →
    y ≠ (block528S3 : ℝ) → y ≠ (block528S4 : ℝ) → 0 < block528V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block528RightL : ℝ) (block528RightR : ℝ) →
    y ≠ 0 → y ≠ (block528S1 : ℝ) → y ≠ (block528S2 : ℝ) →
    y ≠ (block528S3 : ℝ) → y ≠ (block528S4 : ℝ) → 0 < block528V y)

theorem block528_reallog_certificate_proof :
    block528_reallog_certificate := by
  exact ⟨block528_left_V_pos, block528_right_V_pos⟩

end Block528
end M1817475
end Erdos1038Lean
