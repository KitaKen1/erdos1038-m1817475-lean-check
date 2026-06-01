import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block271

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block271

open Set

def block271W1 : Rat := ((10288571218228673 : Rat) / 10000000000000000)
def block271W2 : Rat := ((29499282902977663 : Rat) / 1000000000000000000)
def block271W3 : Rat := ((2923701810786573 : Rat) / 10000000000000000)
def block271W4 : Rat := (0 : Rat)
def block271S1 : Rat := ((18174751 : Rat) / 10000000)
def block271S2 : Rat := ((511587 : Rat) / 200000)
def block271S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block271S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block271V (y : ℝ) : ℝ :=
  ratPotential block271W1 block271W2 block271W3 block271W4 block271S1 block271S2 block271S3 block271S4 y

def block271LeftParamsCertificate : Bool :=
  allBoxesSameParams block271LeftBoxes block271W1 block271W2 block271W3 block271W4 block271S1 block271S2 block271S3 block271S4

theorem block271LeftParamsCertificate_eq_true :
    block271LeftParamsCertificate = true := by
  native_decide

theorem block271_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block271LeftL : ℝ) (block271LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block271S1 : ℝ))
    (hy2ne : y ≠ (block271S2 : ℝ))
    (hy3ne : y ≠ (block271S3 : ℝ))
    (hy4ne : y ≠ (block271S4 : ℝ)) :
    0 < block271V y := by
  have hcert := block271LeftCertificate_eq_true
  unfold block271LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block271LeftBoxes) (lo := block271LeftL) (hi := block271LeftR)
    (w1 := block271W1) (w2 := block271W2) (w3 := block271W3) (w4 := block271W4)
    (s1 := block271S1) (s2 := block271S2) (s3 := block271S3) (s4 := block271S4)
    hboxes hcover block271LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block271RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block271RightChunk000 block271W1 block271W2 block271W3 block271W4 block271S1 block271S2 block271S3 block271S4

theorem block271RightChunk000ParamsCertificate_eq_true :
    block271RightChunk000ParamsCertificate = true := by
  native_decide

theorem block271_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block271RightChunk000L : ℝ) (block271RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block271S1 : ℝ))
    (hy2ne : y ≠ (block271S2 : ℝ))
    (hy3ne : y ≠ (block271S3 : ℝ))
    (hy4ne : y ≠ (block271S4 : ℝ)) :
    0 < block271V y := by
  have hcert := block271RightChunk000Certificate_eq_true
  unfold block271RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block271RightChunk000) (lo := block271RightChunk000L) (hi := block271RightChunk000R)
    (w1 := block271W1) (w2 := block271W2) (w3 := block271W3) (w4 := block271W4)
    (s1 := block271S1) (s2 := block271S2) (s3 := block271S3) (s4 := block271S4)
    hboxes hcover block271RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block271_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block271RightL : ℝ) (block271RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block271S1 : ℝ))
    (hy2ne : y ≠ (block271S2 : ℝ))
    (hy3ne : y ≠ (block271S3 : ℝ))
    (hy4ne : y ≠ (block271S4 : ℝ)) :
    0 < block271V y := by
  have hL : (block271RightChunk000L : ℝ) = (block271RightL : ℝ) := by
    norm_num [block271RightChunk000L, block271RightL]
  have hR : (block271RightChunk000R : ℝ) = (block271RightR : ℝ) := by
    norm_num [block271RightChunk000R, block271RightR]
  have hyc : y ∈ Icc (block271RightChunk000L : ℝ) (block271RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block271_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block271_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block271LeftL : ℝ) (block271LeftR : ℝ) →
    y ≠ 0 → y ≠ (block271S1 : ℝ) → y ≠ (block271S2 : ℝ) →
    y ≠ (block271S3 : ℝ) → y ≠ (block271S4 : ℝ) → 0 < block271V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block271RightL : ℝ) (block271RightR : ℝ) →
    y ≠ 0 → y ≠ (block271S1 : ℝ) → y ≠ (block271S2 : ℝ) →
    y ≠ (block271S3 : ℝ) → y ≠ (block271S4 : ℝ) → 0 < block271V y)

theorem block271_reallog_certificate_proof :
    block271_reallog_certificate := by
  exact ⟨block271_left_V_pos, block271_right_V_pos⟩

end Block271
end M1817475
end Erdos1038Lean
