import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block150

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block150

open Set

def block150W1 : Rat := ((21712157361539437 : Rat) / 10000000000000000)
def block150W2 : Rat := (0 : Rat)
def block150W3 : Rat := ((1683848014159643 : Rat) / 10000000000000000)
def block150W4 : Rat := ((1050274581883151 : Rat) / 12500000000000000)
def block150S1 : Rat := ((18174751 : Rat) / 10000000)
def block150S2 : Rat := ((511587 : Rat) / 200000)
def block150S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block150S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block150V (y : ℝ) : ℝ :=
  ratPotential block150W1 block150W2 block150W3 block150W4 block150S1 block150S2 block150S3 block150S4 y

def block150LeftParamsCertificate : Bool :=
  allBoxesSameParams block150LeftBoxes block150W1 block150W2 block150W3 block150W4 block150S1 block150S2 block150S3 block150S4

theorem block150LeftParamsCertificate_eq_true :
    block150LeftParamsCertificate = true := by
  native_decide

theorem block150_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block150LeftL : ℝ) (block150LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block150S1 : ℝ))
    (hy2ne : y ≠ (block150S2 : ℝ))
    (hy3ne : y ≠ (block150S3 : ℝ))
    (hy4ne : y ≠ (block150S4 : ℝ)) :
    0 < block150V y := by
  have hcert := block150LeftCertificate_eq_true
  unfold block150LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block150LeftBoxes) (lo := block150LeftL) (hi := block150LeftR)
    (w1 := block150W1) (w2 := block150W2) (w3 := block150W3) (w4 := block150W4)
    (s1 := block150S1) (s2 := block150S2) (s3 := block150S3) (s4 := block150S4)
    hboxes hcover block150LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block150RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block150RightChunk000 block150W1 block150W2 block150W3 block150W4 block150S1 block150S2 block150S3 block150S4

theorem block150RightChunk000ParamsCertificate_eq_true :
    block150RightChunk000ParamsCertificate = true := by
  native_decide

theorem block150_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block150RightChunk000L : ℝ) (block150RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block150S1 : ℝ))
    (hy2ne : y ≠ (block150S2 : ℝ))
    (hy3ne : y ≠ (block150S3 : ℝ))
    (hy4ne : y ≠ (block150S4 : ℝ)) :
    0 < block150V y := by
  have hcert := block150RightChunk000Certificate_eq_true
  unfold block150RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block150RightChunk000) (lo := block150RightChunk000L) (hi := block150RightChunk000R)
    (w1 := block150W1) (w2 := block150W2) (w3 := block150W3) (w4 := block150W4)
    (s1 := block150S1) (s2 := block150S2) (s3 := block150S3) (s4 := block150S4)
    hboxes hcover block150RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block150_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block150RightL : ℝ) (block150RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block150S1 : ℝ))
    (hy2ne : y ≠ (block150S2 : ℝ))
    (hy3ne : y ≠ (block150S3 : ℝ))
    (hy4ne : y ≠ (block150S4 : ℝ)) :
    0 < block150V y := by
  have hL : (block150RightChunk000L : ℝ) = (block150RightL : ℝ) := by
    norm_num [block150RightChunk000L, block150RightL]
  have hR : (block150RightChunk000R : ℝ) = (block150RightR : ℝ) := by
    norm_num [block150RightChunk000R, block150RightR]
  have hyc : y ∈ Icc (block150RightChunk000L : ℝ) (block150RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block150_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block150_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block150LeftL : ℝ) (block150LeftR : ℝ) →
    y ≠ 0 → y ≠ (block150S1 : ℝ) → y ≠ (block150S2 : ℝ) →
    y ≠ (block150S3 : ℝ) → y ≠ (block150S4 : ℝ) → 0 < block150V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block150RightL : ℝ) (block150RightR : ℝ) →
    y ≠ 0 → y ≠ (block150S1 : ℝ) → y ≠ (block150S2 : ℝ) →
    y ≠ (block150S3 : ℝ) → y ≠ (block150S4 : ℝ) → 0 < block150V y)

theorem block150_reallog_certificate_proof :
    block150_reallog_certificate := by
  exact ⟨block150_left_V_pos, block150_right_V_pos⟩

end Block150
end M1817475
end Erdos1038Lean
