import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block274

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block274

open Set

def block274W1 : Rat := ((5145152316669953 : Rat) / 5000000000000000)
def block274W2 : Rat := ((30739913052925973 : Rat) / 1000000000000000000)
def block274W3 : Rat := ((7260126985933589 : Rat) / 25000000000000000)
def block274W4 : Rat := (0 : Rat)
def block274S1 : Rat := ((18174751 : Rat) / 10000000)
def block274S2 : Rat := ((511587 : Rat) / 200000)
def block274S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block274S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block274V (y : ℝ) : ℝ :=
  ratPotential block274W1 block274W2 block274W3 block274W4 block274S1 block274S2 block274S3 block274S4 y

def block274LeftParamsCertificate : Bool :=
  allBoxesSameParams block274LeftBoxes block274W1 block274W2 block274W3 block274W4 block274S1 block274S2 block274S3 block274S4

theorem block274LeftParamsCertificate_eq_true :
    block274LeftParamsCertificate = true := by
  native_decide

theorem block274_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block274LeftL : ℝ) (block274LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block274S1 : ℝ))
    (hy2ne : y ≠ (block274S2 : ℝ))
    (hy3ne : y ≠ (block274S3 : ℝ))
    (hy4ne : y ≠ (block274S4 : ℝ)) :
    0 < block274V y := by
  have hcert := block274LeftCertificate_eq_true
  unfold block274LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block274LeftBoxes) (lo := block274LeftL) (hi := block274LeftR)
    (w1 := block274W1) (w2 := block274W2) (w3 := block274W3) (w4 := block274W4)
    (s1 := block274S1) (s2 := block274S2) (s3 := block274S3) (s4 := block274S4)
    hboxes hcover block274LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block274RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block274RightChunk000 block274W1 block274W2 block274W3 block274W4 block274S1 block274S2 block274S3 block274S4

theorem block274RightChunk000ParamsCertificate_eq_true :
    block274RightChunk000ParamsCertificate = true := by
  native_decide

theorem block274_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block274RightChunk000L : ℝ) (block274RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block274S1 : ℝ))
    (hy2ne : y ≠ (block274S2 : ℝ))
    (hy3ne : y ≠ (block274S3 : ℝ))
    (hy4ne : y ≠ (block274S4 : ℝ)) :
    0 < block274V y := by
  have hcert := block274RightChunk000Certificate_eq_true
  unfold block274RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block274RightChunk000) (lo := block274RightChunk000L) (hi := block274RightChunk000R)
    (w1 := block274W1) (w2 := block274W2) (w3 := block274W3) (w4 := block274W4)
    (s1 := block274S1) (s2 := block274S2) (s3 := block274S3) (s4 := block274S4)
    hboxes hcover block274RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block274_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block274RightL : ℝ) (block274RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block274S1 : ℝ))
    (hy2ne : y ≠ (block274S2 : ℝ))
    (hy3ne : y ≠ (block274S3 : ℝ))
    (hy4ne : y ≠ (block274S4 : ℝ)) :
    0 < block274V y := by
  have hL : (block274RightChunk000L : ℝ) = (block274RightL : ℝ) := by
    norm_num [block274RightChunk000L, block274RightL]
  have hR : (block274RightChunk000R : ℝ) = (block274RightR : ℝ) := by
    norm_num [block274RightChunk000R, block274RightR]
  have hyc : y ∈ Icc (block274RightChunk000L : ℝ) (block274RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block274_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block274_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block274LeftL : ℝ) (block274LeftR : ℝ) →
    y ≠ 0 → y ≠ (block274S1 : ℝ) → y ≠ (block274S2 : ℝ) →
    y ≠ (block274S3 : ℝ) → y ≠ (block274S4 : ℝ) → 0 < block274V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block274RightL : ℝ) (block274RightR : ℝ) →
    y ≠ 0 → y ≠ (block274S1 : ℝ) → y ≠ (block274S2 : ℝ) →
    y ≠ (block274S3 : ℝ) → y ≠ (block274S4 : ℝ) → 0 < block274V y)

theorem block274_reallog_certificate_proof :
    block274_reallog_certificate := by
  exact ⟨block274_left_V_pos, block274_right_V_pos⟩

end Block274
end M1817475
end Erdos1038Lean
