import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block473

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block473

open Set

def block473W1 : Rat := ((1333382295740473 : Rat) / 2500000000000000)
def block473W2 : Rat := (0 : Rat)
def block473W3 : Rat := ((57300132569171 : Rat) / 156250000000000)
def block473W4 : Rat := ((4866242053143227 : Rat) / 100000000000000000)
def block473S1 : Rat := ((18174751 : Rat) / 10000000)
def block473S2 : Rat := ((511587 : Rat) / 200000)
def block473S3 : Rat := ((130886829553571428697 : Rat) / 50000000000000000000)
def block473S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block473V (y : ℝ) : ℝ :=
  ratPotential block473W1 block473W2 block473W3 block473W4 block473S1 block473S2 block473S3 block473S4 y

def block473LeftParamsCertificate : Bool :=
  allBoxesSameParams block473LeftBoxes block473W1 block473W2 block473W3 block473W4 block473S1 block473S2 block473S3 block473S4

theorem block473LeftParamsCertificate_eq_true :
    block473LeftParamsCertificate = true := by
  native_decide

theorem block473_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block473LeftL : ℝ) (block473LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block473S1 : ℝ))
    (hy2ne : y ≠ (block473S2 : ℝ))
    (hy3ne : y ≠ (block473S3 : ℝ))
    (hy4ne : y ≠ (block473S4 : ℝ)) :
    0 < block473V y := by
  have hcert := block473LeftCertificate_eq_true
  unfold block473LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block473LeftBoxes) (lo := block473LeftL) (hi := block473LeftR)
    (w1 := block473W1) (w2 := block473W2) (w3 := block473W3) (w4 := block473W4)
    (s1 := block473S1) (s2 := block473S2) (s3 := block473S3) (s4 := block473S4)
    hboxes hcover block473LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block473RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block473RightChunk000 block473W1 block473W2 block473W3 block473W4 block473S1 block473S2 block473S3 block473S4

theorem block473RightChunk000ParamsCertificate_eq_true :
    block473RightChunk000ParamsCertificate = true := by
  native_decide

theorem block473_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block473RightChunk000L : ℝ) (block473RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block473S1 : ℝ))
    (hy2ne : y ≠ (block473S2 : ℝ))
    (hy3ne : y ≠ (block473S3 : ℝ))
    (hy4ne : y ≠ (block473S4 : ℝ)) :
    0 < block473V y := by
  have hcert := block473RightChunk000Certificate_eq_true
  unfold block473RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block473RightChunk000) (lo := block473RightChunk000L) (hi := block473RightChunk000R)
    (w1 := block473W1) (w2 := block473W2) (w3 := block473W3) (w4 := block473W4)
    (s1 := block473S1) (s2 := block473S2) (s3 := block473S3) (s4 := block473S4)
    hboxes hcover block473RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block473_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block473RightL : ℝ) (block473RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block473S1 : ℝ))
    (hy2ne : y ≠ (block473S2 : ℝ))
    (hy3ne : y ≠ (block473S3 : ℝ))
    (hy4ne : y ≠ (block473S4 : ℝ)) :
    0 < block473V y := by
  have hL : (block473RightChunk000L : ℝ) = (block473RightL : ℝ) := by
    norm_num [block473RightChunk000L, block473RightL]
  have hR : (block473RightChunk000R : ℝ) = (block473RightR : ℝ) := by
    norm_num [block473RightChunk000R, block473RightR]
  have hyc : y ∈ Icc (block473RightChunk000L : ℝ) (block473RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block473_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block473_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block473LeftL : ℝ) (block473LeftR : ℝ) →
    y ≠ 0 → y ≠ (block473S1 : ℝ) → y ≠ (block473S2 : ℝ) →
    y ≠ (block473S3 : ℝ) → y ≠ (block473S4 : ℝ) → 0 < block473V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block473RightL : ℝ) (block473RightR : ℝ) →
    y ≠ 0 → y ≠ (block473S1 : ℝ) → y ≠ (block473S2 : ℝ) →
    y ≠ (block473S3 : ℝ) → y ≠ (block473S4 : ℝ) → 0 < block473V y)

theorem block473_reallog_certificate_proof :
    block473_reallog_certificate := by
  exact ⟨block473_left_V_pos, block473_right_V_pos⟩

end Block473
end M1817475
end Erdos1038Lean
