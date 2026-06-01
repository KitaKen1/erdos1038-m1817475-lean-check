import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block105

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block105

open Set

def block105W1 : Rat := ((5185243534576613 : Rat) / 2000000000000000)
def block105W2 : Rat := (0 : Rat)
def block105W3 : Rat := ((2778076309040967 : Rat) / 50000000000000000)
def block105W4 : Rat := ((19108072019443623 : Rat) / 100000000000000000)
def block105S1 : Rat := ((18174751 : Rat) / 10000000)
def block105S2 : Rat := ((511587 : Rat) / 200000)
def block105S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block105S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block105V (y : ℝ) : ℝ :=
  ratPotential block105W1 block105W2 block105W3 block105W4 block105S1 block105S2 block105S3 block105S4 y

def block105LeftParamsCertificate : Bool :=
  allBoxesSameParams block105LeftBoxes block105W1 block105W2 block105W3 block105W4 block105S1 block105S2 block105S3 block105S4

theorem block105LeftParamsCertificate_eq_true :
    block105LeftParamsCertificate = true := by
  native_decide

theorem block105_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block105LeftL : ℝ) (block105LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block105S1 : ℝ))
    (hy2ne : y ≠ (block105S2 : ℝ))
    (hy3ne : y ≠ (block105S3 : ℝ))
    (hy4ne : y ≠ (block105S4 : ℝ)) :
    0 < block105V y := by
  have hcert := block105LeftCertificate_eq_true
  unfold block105LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block105LeftBoxes) (lo := block105LeftL) (hi := block105LeftR)
    (w1 := block105W1) (w2 := block105W2) (w3 := block105W3) (w4 := block105W4)
    (s1 := block105S1) (s2 := block105S2) (s3 := block105S3) (s4 := block105S4)
    hboxes hcover block105LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block105RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block105RightChunk000 block105W1 block105W2 block105W3 block105W4 block105S1 block105S2 block105S3 block105S4

theorem block105RightChunk000ParamsCertificate_eq_true :
    block105RightChunk000ParamsCertificate = true := by
  native_decide

theorem block105_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block105RightChunk000L : ℝ) (block105RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block105S1 : ℝ))
    (hy2ne : y ≠ (block105S2 : ℝ))
    (hy3ne : y ≠ (block105S3 : ℝ))
    (hy4ne : y ≠ (block105S4 : ℝ)) :
    0 < block105V y := by
  have hcert := block105RightChunk000Certificate_eq_true
  unfold block105RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block105RightChunk000) (lo := block105RightChunk000L) (hi := block105RightChunk000R)
    (w1 := block105W1) (w2 := block105W2) (w3 := block105W3) (w4 := block105W4)
    (s1 := block105S1) (s2 := block105S2) (s3 := block105S3) (s4 := block105S4)
    hboxes hcover block105RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block105_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block105RightL : ℝ) (block105RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block105S1 : ℝ))
    (hy2ne : y ≠ (block105S2 : ℝ))
    (hy3ne : y ≠ (block105S3 : ℝ))
    (hy4ne : y ≠ (block105S4 : ℝ)) :
    0 < block105V y := by
  have hL : (block105RightChunk000L : ℝ) = (block105RightL : ℝ) := by
    norm_num [block105RightChunk000L, block105RightL]
  have hR : (block105RightChunk000R : ℝ) = (block105RightR : ℝ) := by
    norm_num [block105RightChunk000R, block105RightR]
  have hyc : y ∈ Icc (block105RightChunk000L : ℝ) (block105RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block105_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block105_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block105LeftL : ℝ) (block105LeftR : ℝ) →
    y ≠ 0 → y ≠ (block105S1 : ℝ) → y ≠ (block105S2 : ℝ) →
    y ≠ (block105S3 : ℝ) → y ≠ (block105S4 : ℝ) → 0 < block105V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block105RightL : ℝ) (block105RightR : ℝ) →
    y ≠ 0 → y ≠ (block105S1 : ℝ) → y ≠ (block105S2 : ℝ) →
    y ≠ (block105S3 : ℝ) → y ≠ (block105S4 : ℝ) → 0 < block105V y)

theorem block105_reallog_certificate_proof :
    block105_reallog_certificate := by
  exact ⟨block105_left_V_pos, block105_right_V_pos⟩

end Block105
end M1817475
end Erdos1038Lean
