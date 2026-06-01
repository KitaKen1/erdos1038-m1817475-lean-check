import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block141

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block141

open Set

def block141W1 : Rat := ((627819450325797 : Rat) / 250000000000000)
def block141W2 : Rat := (0 : Rat)
def block141W3 : Rat := ((2478944697969967 : Rat) / 20000000000000000)
def block141W4 : Rat := ((11524534453781879 : Rat) / 100000000000000000)
def block141S1 : Rat := ((18174751 : Rat) / 10000000)
def block141S2 : Rat := ((511587 : Rat) / 200000)
def block141S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block141S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block141V (y : ℝ) : ℝ :=
  ratPotential block141W1 block141W2 block141W3 block141W4 block141S1 block141S2 block141S3 block141S4 y

def block141LeftParamsCertificate : Bool :=
  allBoxesSameParams block141LeftBoxes block141W1 block141W2 block141W3 block141W4 block141S1 block141S2 block141S3 block141S4

theorem block141LeftParamsCertificate_eq_true :
    block141LeftParamsCertificate = true := by
  native_decide

theorem block141_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block141LeftL : ℝ) (block141LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block141S1 : ℝ))
    (hy2ne : y ≠ (block141S2 : ℝ))
    (hy3ne : y ≠ (block141S3 : ℝ))
    (hy4ne : y ≠ (block141S4 : ℝ)) :
    0 < block141V y := by
  have hcert := block141LeftCertificate_eq_true
  unfold block141LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block141LeftBoxes) (lo := block141LeftL) (hi := block141LeftR)
    (w1 := block141W1) (w2 := block141W2) (w3 := block141W3) (w4 := block141W4)
    (s1 := block141S1) (s2 := block141S2) (s3 := block141S3) (s4 := block141S4)
    hboxes hcover block141LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block141RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block141RightChunk000 block141W1 block141W2 block141W3 block141W4 block141S1 block141S2 block141S3 block141S4

theorem block141RightChunk000ParamsCertificate_eq_true :
    block141RightChunk000ParamsCertificate = true := by
  native_decide

theorem block141_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block141RightChunk000L : ℝ) (block141RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block141S1 : ℝ))
    (hy2ne : y ≠ (block141S2 : ℝ))
    (hy3ne : y ≠ (block141S3 : ℝ))
    (hy4ne : y ≠ (block141S4 : ℝ)) :
    0 < block141V y := by
  have hcert := block141RightChunk000Certificate_eq_true
  unfold block141RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block141RightChunk000) (lo := block141RightChunk000L) (hi := block141RightChunk000R)
    (w1 := block141W1) (w2 := block141W2) (w3 := block141W3) (w4 := block141W4)
    (s1 := block141S1) (s2 := block141S2) (s3 := block141S3) (s4 := block141S4)
    hboxes hcover block141RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block141_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block141RightL : ℝ) (block141RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block141S1 : ℝ))
    (hy2ne : y ≠ (block141S2 : ℝ))
    (hy3ne : y ≠ (block141S3 : ℝ))
    (hy4ne : y ≠ (block141S4 : ℝ)) :
    0 < block141V y := by
  have hL : (block141RightChunk000L : ℝ) = (block141RightL : ℝ) := by
    norm_num [block141RightChunk000L, block141RightL]
  have hR : (block141RightChunk000R : ℝ) = (block141RightR : ℝ) := by
    norm_num [block141RightChunk000R, block141RightR]
  have hyc : y ∈ Icc (block141RightChunk000L : ℝ) (block141RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block141_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block141_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block141LeftL : ℝ) (block141LeftR : ℝ) →
    y ≠ 0 → y ≠ (block141S1 : ℝ) → y ≠ (block141S2 : ℝ) →
    y ≠ (block141S3 : ℝ) → y ≠ (block141S4 : ℝ) → 0 < block141V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block141RightL : ℝ) (block141RightR : ℝ) →
    y ≠ 0 → y ≠ (block141S1 : ℝ) → y ≠ (block141S2 : ℝ) →
    y ≠ (block141S3 : ℝ) → y ≠ (block141S4 : ℝ) → 0 < block141V y)

theorem block141_reallog_certificate_proof :
    block141_reallog_certificate := by
  exact ⟨block141_left_V_pos, block141_right_V_pos⟩

end Block141
end M1817475
end Erdos1038Lean
