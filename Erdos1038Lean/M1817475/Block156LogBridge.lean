import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block156

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block156

open Set

def block156W1 : Rat := ((21339714376966143 : Rat) / 10000000000000000)
def block156W2 : Rat := (0 : Rat)
def block156W3 : Rat := ((17321495966075603 : Rat) / 100000000000000000)
def block156W4 : Rat := ((4032810361245051 : Rat) / 50000000000000000)
def block156S1 : Rat := ((18174751 : Rat) / 10000000)
def block156S2 : Rat := ((511587 : Rat) / 200000)
def block156S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block156S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block156V (y : ℝ) : ℝ :=
  ratPotential block156W1 block156W2 block156W3 block156W4 block156S1 block156S2 block156S3 block156S4 y

def block156LeftParamsCertificate : Bool :=
  allBoxesSameParams block156LeftBoxes block156W1 block156W2 block156W3 block156W4 block156S1 block156S2 block156S3 block156S4

theorem block156LeftParamsCertificate_eq_true :
    block156LeftParamsCertificate = true := by
  native_decide

theorem block156_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block156LeftL : ℝ) (block156LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block156S1 : ℝ))
    (hy2ne : y ≠ (block156S2 : ℝ))
    (hy3ne : y ≠ (block156S3 : ℝ))
    (hy4ne : y ≠ (block156S4 : ℝ)) :
    0 < block156V y := by
  have hcert := block156LeftCertificate_eq_true
  unfold block156LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block156LeftBoxes) (lo := block156LeftL) (hi := block156LeftR)
    (w1 := block156W1) (w2 := block156W2) (w3 := block156W3) (w4 := block156W4)
    (s1 := block156S1) (s2 := block156S2) (s3 := block156S3) (s4 := block156S4)
    hboxes hcover block156LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block156RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block156RightChunk000 block156W1 block156W2 block156W3 block156W4 block156S1 block156S2 block156S3 block156S4

theorem block156RightChunk000ParamsCertificate_eq_true :
    block156RightChunk000ParamsCertificate = true := by
  native_decide

theorem block156_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block156RightChunk000L : ℝ) (block156RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block156S1 : ℝ))
    (hy2ne : y ≠ (block156S2 : ℝ))
    (hy3ne : y ≠ (block156S3 : ℝ))
    (hy4ne : y ≠ (block156S4 : ℝ)) :
    0 < block156V y := by
  have hcert := block156RightChunk000Certificate_eq_true
  unfold block156RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block156RightChunk000) (lo := block156RightChunk000L) (hi := block156RightChunk000R)
    (w1 := block156W1) (w2 := block156W2) (w3 := block156W3) (w4 := block156W4)
    (s1 := block156S1) (s2 := block156S2) (s3 := block156S3) (s4 := block156S4)
    hboxes hcover block156RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block156_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block156RightL : ℝ) (block156RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block156S1 : ℝ))
    (hy2ne : y ≠ (block156S2 : ℝ))
    (hy3ne : y ≠ (block156S3 : ℝ))
    (hy4ne : y ≠ (block156S4 : ℝ)) :
    0 < block156V y := by
  have hL : (block156RightChunk000L : ℝ) = (block156RightL : ℝ) := by
    norm_num [block156RightChunk000L, block156RightL]
  have hR : (block156RightChunk000R : ℝ) = (block156RightR : ℝ) := by
    norm_num [block156RightChunk000R, block156RightR]
  have hyc : y ∈ Icc (block156RightChunk000L : ℝ) (block156RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block156_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block156_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block156LeftL : ℝ) (block156LeftR : ℝ) →
    y ≠ 0 → y ≠ (block156S1 : ℝ) → y ≠ (block156S2 : ℝ) →
    y ≠ (block156S3 : ℝ) → y ≠ (block156S4 : ℝ) → 0 < block156V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block156RightL : ℝ) (block156RightR : ℝ) →
    y ≠ 0 → y ≠ (block156S1 : ℝ) → y ≠ (block156S2 : ℝ) →
    y ≠ (block156S3 : ℝ) → y ≠ (block156S4 : ℝ) → 0 < block156V y)

theorem block156_reallog_certificate_proof :
    block156_reallog_certificate := by
  exact ⟨block156_left_V_pos, block156_right_V_pos⟩

end Block156
end M1817475
end Erdos1038Lean
