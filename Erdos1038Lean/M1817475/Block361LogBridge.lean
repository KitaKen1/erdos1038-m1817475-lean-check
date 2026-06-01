import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block361

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block361

open Set

def block361W1 : Rat := ((4422370922088137 : Rat) / 5000000000000000)
def block361W2 : Rat := ((189676467722041 : Rat) / 4000000000000000)
def block361W3 : Rat := ((1901472248171493 : Rat) / 12500000000000000)
def block361W4 : Rat := ((3476999445786423 : Rat) / 25000000000000000)
def block361S1 : Rat := ((18174751 : Rat) / 10000000)
def block361S2 : Rat := ((511587 : Rat) / 200000)
def block361S3 : Rat := ((133076329553571428601 : Rat) / 50000000000000000000)
def block361S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block361V (y : ℝ) : ℝ :=
  ratPotential block361W1 block361W2 block361W3 block361W4 block361S1 block361S2 block361S3 block361S4 y

def block361LeftParamsCertificate : Bool :=
  allBoxesSameParams block361LeftBoxes block361W1 block361W2 block361W3 block361W4 block361S1 block361S2 block361S3 block361S4

theorem block361LeftParamsCertificate_eq_true :
    block361LeftParamsCertificate = true := by
  native_decide

theorem block361_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block361LeftL : ℝ) (block361LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block361S1 : ℝ))
    (hy2ne : y ≠ (block361S2 : ℝ))
    (hy3ne : y ≠ (block361S3 : ℝ))
    (hy4ne : y ≠ (block361S4 : ℝ)) :
    0 < block361V y := by
  have hcert := block361LeftCertificate_eq_true
  unfold block361LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block361LeftBoxes) (lo := block361LeftL) (hi := block361LeftR)
    (w1 := block361W1) (w2 := block361W2) (w3 := block361W3) (w4 := block361W4)
    (s1 := block361S1) (s2 := block361S2) (s3 := block361S3) (s4 := block361S4)
    hboxes hcover block361LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block361RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block361RightChunk000 block361W1 block361W2 block361W3 block361W4 block361S1 block361S2 block361S3 block361S4

theorem block361RightChunk000ParamsCertificate_eq_true :
    block361RightChunk000ParamsCertificate = true := by
  native_decide

theorem block361_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block361RightChunk000L : ℝ) (block361RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block361S1 : ℝ))
    (hy2ne : y ≠ (block361S2 : ℝ))
    (hy3ne : y ≠ (block361S3 : ℝ))
    (hy4ne : y ≠ (block361S4 : ℝ)) :
    0 < block361V y := by
  have hcert := block361RightChunk000Certificate_eq_true
  unfold block361RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block361RightChunk000) (lo := block361RightChunk000L) (hi := block361RightChunk000R)
    (w1 := block361W1) (w2 := block361W2) (w3 := block361W3) (w4 := block361W4)
    (s1 := block361S1) (s2 := block361S2) (s3 := block361S3) (s4 := block361S4)
    hboxes hcover block361RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block361_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block361RightL : ℝ) (block361RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block361S1 : ℝ))
    (hy2ne : y ≠ (block361S2 : ℝ))
    (hy3ne : y ≠ (block361S3 : ℝ))
    (hy4ne : y ≠ (block361S4 : ℝ)) :
    0 < block361V y := by
  have hL : (block361RightChunk000L : ℝ) = (block361RightL : ℝ) := by
    norm_num [block361RightChunk000L, block361RightL]
  have hR : (block361RightChunk000R : ℝ) = (block361RightR : ℝ) := by
    norm_num [block361RightChunk000R, block361RightR]
  have hyc : y ∈ Icc (block361RightChunk000L : ℝ) (block361RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block361_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block361_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block361LeftL : ℝ) (block361LeftR : ℝ) →
    y ≠ 0 → y ≠ (block361S1 : ℝ) → y ≠ (block361S2 : ℝ) →
    y ≠ (block361S3 : ℝ) → y ≠ (block361S4 : ℝ) → 0 < block361V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block361RightL : ℝ) (block361RightR : ℝ) →
    y ≠ 0 → y ≠ (block361S1 : ℝ) → y ≠ (block361S2 : ℝ) →
    y ≠ (block361S3 : ℝ) → y ≠ (block361S4 : ℝ) → 0 < block361V y)

theorem block361_reallog_certificate_proof :
    block361_reallog_certificate := by
  exact ⟨block361_left_V_pos, block361_right_V_pos⟩

end Block361
end M1817475
end Erdos1038Lean
