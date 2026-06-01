import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block368

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block368

open Set

def block368W1 : Rat := ((871138529224949 : Rat) / 1000000000000000)
def block368W2 : Rat := ((4724289277198759 : Rat) / 100000000000000000)
def block368W3 : Rat := ((7710250745715133 : Rat) / 50000000000000000)
def block368W4 : Rat := ((6979772679729647 : Rat) / 50000000000000000)
def block368S1 : Rat := ((18174751 : Rat) / 10000000)
def block368S2 : Rat := ((511587 : Rat) / 200000)
def block368S3 : Rat := ((132939485803571428607 : Rat) / 50000000000000000000)
def block368S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block368V (y : ℝ) : ℝ :=
  ratPotential block368W1 block368W2 block368W3 block368W4 block368S1 block368S2 block368S3 block368S4 y

def block368LeftParamsCertificate : Bool :=
  allBoxesSameParams block368LeftBoxes block368W1 block368W2 block368W3 block368W4 block368S1 block368S2 block368S3 block368S4

theorem block368LeftParamsCertificate_eq_true :
    block368LeftParamsCertificate = true := by
  native_decide

theorem block368_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block368LeftL : ℝ) (block368LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block368S1 : ℝ))
    (hy2ne : y ≠ (block368S2 : ℝ))
    (hy3ne : y ≠ (block368S3 : ℝ))
    (hy4ne : y ≠ (block368S4 : ℝ)) :
    0 < block368V y := by
  have hcert := block368LeftCertificate_eq_true
  unfold block368LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block368LeftBoxes) (lo := block368LeftL) (hi := block368LeftR)
    (w1 := block368W1) (w2 := block368W2) (w3 := block368W3) (w4 := block368W4)
    (s1 := block368S1) (s2 := block368S2) (s3 := block368S3) (s4 := block368S4)
    hboxes hcover block368LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block368RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block368RightChunk000 block368W1 block368W2 block368W3 block368W4 block368S1 block368S2 block368S3 block368S4

theorem block368RightChunk000ParamsCertificate_eq_true :
    block368RightChunk000ParamsCertificate = true := by
  native_decide

theorem block368_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block368RightChunk000L : ℝ) (block368RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block368S1 : ℝ))
    (hy2ne : y ≠ (block368S2 : ℝ))
    (hy3ne : y ≠ (block368S3 : ℝ))
    (hy4ne : y ≠ (block368S4 : ℝ)) :
    0 < block368V y := by
  have hcert := block368RightChunk000Certificate_eq_true
  unfold block368RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block368RightChunk000) (lo := block368RightChunk000L) (hi := block368RightChunk000R)
    (w1 := block368W1) (w2 := block368W2) (w3 := block368W3) (w4 := block368W4)
    (s1 := block368S1) (s2 := block368S2) (s3 := block368S3) (s4 := block368S4)
    hboxes hcover block368RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block368_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block368RightL : ℝ) (block368RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block368S1 : ℝ))
    (hy2ne : y ≠ (block368S2 : ℝ))
    (hy3ne : y ≠ (block368S3 : ℝ))
    (hy4ne : y ≠ (block368S4 : ℝ)) :
    0 < block368V y := by
  have hL : (block368RightChunk000L : ℝ) = (block368RightL : ℝ) := by
    norm_num [block368RightChunk000L, block368RightL]
  have hR : (block368RightChunk000R : ℝ) = (block368RightR : ℝ) := by
    norm_num [block368RightChunk000R, block368RightR]
  have hyc : y ∈ Icc (block368RightChunk000L : ℝ) (block368RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block368_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block368_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block368LeftL : ℝ) (block368LeftR : ℝ) →
    y ≠ 0 → y ≠ (block368S1 : ℝ) → y ≠ (block368S2 : ℝ) →
    y ≠ (block368S3 : ℝ) → y ≠ (block368S4 : ℝ) → 0 < block368V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block368RightL : ℝ) (block368RightR : ℝ) →
    y ≠ 0 → y ≠ (block368S1 : ℝ) → y ≠ (block368S2 : ℝ) →
    y ≠ (block368S3 : ℝ) → y ≠ (block368S4 : ℝ) → 0 < block368V y)

theorem block368_reallog_certificate_proof :
    block368_reallog_certificate := by
  exact ⟨block368_left_V_pos, block368_right_V_pos⟩

end Block368
end M1817475
end Erdos1038Lean
