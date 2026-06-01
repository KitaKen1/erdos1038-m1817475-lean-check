import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block157

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block157

open Set

def block157W1 : Rat := ((3747861031135547 : Rat) / 2000000000000000)
def block157W2 : Rat := (0 : Rat)
def block157W3 : Rat := ((99758724846609 : Rat) / 625000000000000)
def block157W4 : Rat := ((2141100548153587 : Rat) / 20000000000000000)
def block157S1 : Rat := ((18174751 : Rat) / 10000000)
def block157S2 : Rat := ((511587 : Rat) / 200000)
def block157S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block157S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block157V (y : ℝ) : ℝ :=
  ratPotential block157W1 block157W2 block157W3 block157W4 block157S1 block157S2 block157S3 block157S4 y

def block157LeftParamsCertificate : Bool :=
  allBoxesSameParams block157LeftBoxes block157W1 block157W2 block157W3 block157W4 block157S1 block157S2 block157S3 block157S4

theorem block157LeftParamsCertificate_eq_true :
    block157LeftParamsCertificate = true := by
  native_decide

theorem block157_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block157LeftL : ℝ) (block157LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block157S1 : ℝ))
    (hy2ne : y ≠ (block157S2 : ℝ))
    (hy3ne : y ≠ (block157S3 : ℝ))
    (hy4ne : y ≠ (block157S4 : ℝ)) :
    0 < block157V y := by
  have hcert := block157LeftCertificate_eq_true
  unfold block157LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block157LeftBoxes) (lo := block157LeftL) (hi := block157LeftR)
    (w1 := block157W1) (w2 := block157W2) (w3 := block157W3) (w4 := block157W4)
    (s1 := block157S1) (s2 := block157S2) (s3 := block157S3) (s4 := block157S4)
    hboxes hcover block157LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block157RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block157RightChunk000 block157W1 block157W2 block157W3 block157W4 block157S1 block157S2 block157S3 block157S4

theorem block157RightChunk000ParamsCertificate_eq_true :
    block157RightChunk000ParamsCertificate = true := by
  native_decide

theorem block157_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block157RightChunk000L : ℝ) (block157RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block157S1 : ℝ))
    (hy2ne : y ≠ (block157S2 : ℝ))
    (hy3ne : y ≠ (block157S3 : ℝ))
    (hy4ne : y ≠ (block157S4 : ℝ)) :
    0 < block157V y := by
  have hcert := block157RightChunk000Certificate_eq_true
  unfold block157RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block157RightChunk000) (lo := block157RightChunk000L) (hi := block157RightChunk000R)
    (w1 := block157W1) (w2 := block157W2) (w3 := block157W3) (w4 := block157W4)
    (s1 := block157S1) (s2 := block157S2) (s3 := block157S3) (s4 := block157S4)
    hboxes hcover block157RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block157_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block157RightL : ℝ) (block157RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block157S1 : ℝ))
    (hy2ne : y ≠ (block157S2 : ℝ))
    (hy3ne : y ≠ (block157S3 : ℝ))
    (hy4ne : y ≠ (block157S4 : ℝ)) :
    0 < block157V y := by
  have hL : (block157RightChunk000L : ℝ) = (block157RightL : ℝ) := by
    norm_num [block157RightChunk000L, block157RightL]
  have hR : (block157RightChunk000R : ℝ) = (block157RightR : ℝ) := by
    norm_num [block157RightChunk000R, block157RightR]
  have hyc : y ∈ Icc (block157RightChunk000L : ℝ) (block157RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block157_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block157_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block157LeftL : ℝ) (block157LeftR : ℝ) →
    y ≠ 0 → y ≠ (block157S1 : ℝ) → y ≠ (block157S2 : ℝ) →
    y ≠ (block157S3 : ℝ) → y ≠ (block157S4 : ℝ) → 0 < block157V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block157RightL : ℝ) (block157RightR : ℝ) →
    y ≠ 0 → y ≠ (block157S1 : ℝ) → y ≠ (block157S2 : ℝ) →
    y ≠ (block157S3 : ℝ) → y ≠ (block157S4 : ℝ) → 0 < block157V y)

theorem block157_reallog_certificate_proof :
    block157_reallog_certificate := by
  exact ⟨block157_left_V_pos, block157_right_V_pos⟩

end Block157
end M1817475
end Erdos1038Lean
