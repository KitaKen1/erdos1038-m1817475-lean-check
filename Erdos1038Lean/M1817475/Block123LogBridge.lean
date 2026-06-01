import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block123

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block123

open Set

def block123W1 : Rat := ((4517730843067489 : Rat) / 2000000000000000)
def block123W2 : Rat := (0 : Rat)
def block123W3 : Rat := ((5067623774674567 : Rat) / 50000000000000000)
def block123W4 : Rat := ((944881967181567 : Rat) / 6250000000000000)
def block123S1 : Rat := ((18174751 : Rat) / 10000000)
def block123S2 : Rat := ((511587 : Rat) / 200000)
def block123S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block123S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block123V (y : ℝ) : ℝ :=
  ratPotential block123W1 block123W2 block123W3 block123W4 block123S1 block123S2 block123S3 block123S4 y

def block123LeftParamsCertificate : Bool :=
  allBoxesSameParams block123LeftBoxes block123W1 block123W2 block123W3 block123W4 block123S1 block123S2 block123S3 block123S4

theorem block123LeftParamsCertificate_eq_true :
    block123LeftParamsCertificate = true := by
  native_decide

theorem block123_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block123LeftL : ℝ) (block123LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block123S1 : ℝ))
    (hy2ne : y ≠ (block123S2 : ℝ))
    (hy3ne : y ≠ (block123S3 : ℝ))
    (hy4ne : y ≠ (block123S4 : ℝ)) :
    0 < block123V y := by
  have hcert := block123LeftCertificate_eq_true
  unfold block123LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block123LeftBoxes) (lo := block123LeftL) (hi := block123LeftR)
    (w1 := block123W1) (w2 := block123W2) (w3 := block123W3) (w4 := block123W4)
    (s1 := block123S1) (s2 := block123S2) (s3 := block123S3) (s4 := block123S4)
    hboxes hcover block123LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block123RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block123RightChunk000 block123W1 block123W2 block123W3 block123W4 block123S1 block123S2 block123S3 block123S4

theorem block123RightChunk000ParamsCertificate_eq_true :
    block123RightChunk000ParamsCertificate = true := by
  native_decide

theorem block123_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block123RightChunk000L : ℝ) (block123RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block123S1 : ℝ))
    (hy2ne : y ≠ (block123S2 : ℝ))
    (hy3ne : y ≠ (block123S3 : ℝ))
    (hy4ne : y ≠ (block123S4 : ℝ)) :
    0 < block123V y := by
  have hcert := block123RightChunk000Certificate_eq_true
  unfold block123RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block123RightChunk000) (lo := block123RightChunk000L) (hi := block123RightChunk000R)
    (w1 := block123W1) (w2 := block123W2) (w3 := block123W3) (w4 := block123W4)
    (s1 := block123S1) (s2 := block123S2) (s3 := block123S3) (s4 := block123S4)
    hboxes hcover block123RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block123_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block123RightL : ℝ) (block123RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block123S1 : ℝ))
    (hy2ne : y ≠ (block123S2 : ℝ))
    (hy3ne : y ≠ (block123S3 : ℝ))
    (hy4ne : y ≠ (block123S4 : ℝ)) :
    0 < block123V y := by
  have hL : (block123RightChunk000L : ℝ) = (block123RightL : ℝ) := by
    norm_num [block123RightChunk000L, block123RightL]
  have hR : (block123RightChunk000R : ℝ) = (block123RightR : ℝ) := by
    norm_num [block123RightChunk000R, block123RightR]
  have hyc : y ∈ Icc (block123RightChunk000L : ℝ) (block123RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block123_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block123_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block123LeftL : ℝ) (block123LeftR : ℝ) →
    y ≠ 0 → y ≠ (block123S1 : ℝ) → y ≠ (block123S2 : ℝ) →
    y ≠ (block123S3 : ℝ) → y ≠ (block123S4 : ℝ) → 0 < block123V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block123RightL : ℝ) (block123RightR : ℝ) →
    y ≠ 0 → y ≠ (block123S1 : ℝ) → y ≠ (block123S2 : ℝ) →
    y ≠ (block123S3 : ℝ) → y ≠ (block123S4 : ℝ) → 0 < block123V y)

theorem block123_reallog_certificate_proof :
    block123_reallog_certificate := by
  exact ⟨block123_left_V_pos, block123_right_V_pos⟩

end Block123
end M1817475
end Erdos1038Lean
