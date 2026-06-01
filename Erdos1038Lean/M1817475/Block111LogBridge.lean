import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block111

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block111

open Set

def block111W1 : Rat := ((12581320908151399 : Rat) / 5000000000000000)
def block111W2 : Rat := (0 : Rat)
def block111W3 : Rat := ((1680427322491631 : Rat) / 25000000000000000)
def block111W4 : Rat := ((56119845540779 : Rat) / 312500000000000)
def block111S1 : Rat := ((18174751 : Rat) / 10000000)
def block111S2 : Rat := ((511587 : Rat) / 200000)
def block111S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block111S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block111V (y : ℝ) : ℝ :=
  ratPotential block111W1 block111W2 block111W3 block111W4 block111S1 block111S2 block111S3 block111S4 y

def block111LeftParamsCertificate : Bool :=
  allBoxesSameParams block111LeftBoxes block111W1 block111W2 block111W3 block111W4 block111S1 block111S2 block111S3 block111S4

theorem block111LeftParamsCertificate_eq_true :
    block111LeftParamsCertificate = true := by
  native_decide

theorem block111_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block111LeftL : ℝ) (block111LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block111S1 : ℝ))
    (hy2ne : y ≠ (block111S2 : ℝ))
    (hy3ne : y ≠ (block111S3 : ℝ))
    (hy4ne : y ≠ (block111S4 : ℝ)) :
    0 < block111V y := by
  have hcert := block111LeftCertificate_eq_true
  unfold block111LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block111LeftBoxes) (lo := block111LeftL) (hi := block111LeftR)
    (w1 := block111W1) (w2 := block111W2) (w3 := block111W3) (w4 := block111W4)
    (s1 := block111S1) (s2 := block111S2) (s3 := block111S3) (s4 := block111S4)
    hboxes hcover block111LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block111RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block111RightChunk000 block111W1 block111W2 block111W3 block111W4 block111S1 block111S2 block111S3 block111S4

theorem block111RightChunk000ParamsCertificate_eq_true :
    block111RightChunk000ParamsCertificate = true := by
  native_decide

theorem block111_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block111RightChunk000L : ℝ) (block111RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block111S1 : ℝ))
    (hy2ne : y ≠ (block111S2 : ℝ))
    (hy3ne : y ≠ (block111S3 : ℝ))
    (hy4ne : y ≠ (block111S4 : ℝ)) :
    0 < block111V y := by
  have hcert := block111RightChunk000Certificate_eq_true
  unfold block111RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block111RightChunk000) (lo := block111RightChunk000L) (hi := block111RightChunk000R)
    (w1 := block111W1) (w2 := block111W2) (w3 := block111W3) (w4 := block111W4)
    (s1 := block111S1) (s2 := block111S2) (s3 := block111S3) (s4 := block111S4)
    hboxes hcover block111RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block111_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block111RightL : ℝ) (block111RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block111S1 : ℝ))
    (hy2ne : y ≠ (block111S2 : ℝ))
    (hy3ne : y ≠ (block111S3 : ℝ))
    (hy4ne : y ≠ (block111S4 : ℝ)) :
    0 < block111V y := by
  have hL : (block111RightChunk000L : ℝ) = (block111RightL : ℝ) := by
    norm_num [block111RightChunk000L, block111RightL]
  have hR : (block111RightChunk000R : ℝ) = (block111RightR : ℝ) := by
    norm_num [block111RightChunk000R, block111RightR]
  have hyc : y ∈ Icc (block111RightChunk000L : ℝ) (block111RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block111_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block111_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block111LeftL : ℝ) (block111LeftR : ℝ) →
    y ≠ 0 → y ≠ (block111S1 : ℝ) → y ≠ (block111S2 : ℝ) →
    y ≠ (block111S3 : ℝ) → y ≠ (block111S4 : ℝ) → 0 < block111V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block111RightL : ℝ) (block111RightR : ℝ) →
    y ≠ 0 → y ≠ (block111S1 : ℝ) → y ≠ (block111S2 : ℝ) →
    y ≠ (block111S3 : ℝ) → y ≠ (block111S4 : ℝ) → 0 < block111V y)

theorem block111_reallog_certificate_proof :
    block111_reallog_certificate := by
  exact ⟨block111_left_V_pos, block111_right_V_pos⟩

end Block111
end M1817475
end Erdos1038Lean
