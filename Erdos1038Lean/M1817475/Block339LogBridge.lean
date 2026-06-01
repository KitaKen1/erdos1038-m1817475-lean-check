import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block339

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block339

open Set

def block339W1 : Rat := ((2324108056861463 : Rat) / 2500000000000000)
def block339W2 : Rat := ((236941227765127 : Rat) / 5000000000000000)
def block339W3 : Rat := ((14592990817425333 : Rat) / 100000000000000000)
def block339W4 : Rat := ((1717675700033993 : Rat) / 12500000000000000)
def block339S1 : Rat := ((18174751 : Rat) / 10000000)
def block339S2 : Rat := ((511587 : Rat) / 200000)
def block339S3 : Rat := ((5340256396428571429 : Rat) / 2000000000000000000)
def block339S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block339V (y : ℝ) : ℝ :=
  ratPotential block339W1 block339W2 block339W3 block339W4 block339S1 block339S2 block339S3 block339S4 y

def block339LeftParamsCertificate : Bool :=
  allBoxesSameParams block339LeftBoxes block339W1 block339W2 block339W3 block339W4 block339S1 block339S2 block339S3 block339S4

theorem block339LeftParamsCertificate_eq_true :
    block339LeftParamsCertificate = true := by
  native_decide

theorem block339_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block339LeftL : ℝ) (block339LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block339S1 : ℝ))
    (hy2ne : y ≠ (block339S2 : ℝ))
    (hy3ne : y ≠ (block339S3 : ℝ))
    (hy4ne : y ≠ (block339S4 : ℝ)) :
    0 < block339V y := by
  have hcert := block339LeftCertificate_eq_true
  unfold block339LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block339LeftBoxes) (lo := block339LeftL) (hi := block339LeftR)
    (w1 := block339W1) (w2 := block339W2) (w3 := block339W3) (w4 := block339W4)
    (s1 := block339S1) (s2 := block339S2) (s3 := block339S3) (s4 := block339S4)
    hboxes hcover block339LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block339RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block339RightChunk000 block339W1 block339W2 block339W3 block339W4 block339S1 block339S2 block339S3 block339S4

theorem block339RightChunk000ParamsCertificate_eq_true :
    block339RightChunk000ParamsCertificate = true := by
  native_decide

theorem block339_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block339RightChunk000L : ℝ) (block339RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block339S1 : ℝ))
    (hy2ne : y ≠ (block339S2 : ℝ))
    (hy3ne : y ≠ (block339S3 : ℝ))
    (hy4ne : y ≠ (block339S4 : ℝ)) :
    0 < block339V y := by
  have hcert := block339RightChunk000Certificate_eq_true
  unfold block339RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block339RightChunk000) (lo := block339RightChunk000L) (hi := block339RightChunk000R)
    (w1 := block339W1) (w2 := block339W2) (w3 := block339W3) (w4 := block339W4)
    (s1 := block339S1) (s2 := block339S2) (s3 := block339S3) (s4 := block339S4)
    hboxes hcover block339RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block339_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block339RightL : ℝ) (block339RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block339S1 : ℝ))
    (hy2ne : y ≠ (block339S2 : ℝ))
    (hy3ne : y ≠ (block339S3 : ℝ))
    (hy4ne : y ≠ (block339S4 : ℝ)) :
    0 < block339V y := by
  have hL : (block339RightChunk000L : ℝ) = (block339RightL : ℝ) := by
    norm_num [block339RightChunk000L, block339RightL]
  have hR : (block339RightChunk000R : ℝ) = (block339RightR : ℝ) := by
    norm_num [block339RightChunk000R, block339RightR]
  have hyc : y ∈ Icc (block339RightChunk000L : ℝ) (block339RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block339_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block339_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block339LeftL : ℝ) (block339LeftR : ℝ) →
    y ≠ 0 → y ≠ (block339S1 : ℝ) → y ≠ (block339S2 : ℝ) →
    y ≠ (block339S3 : ℝ) → y ≠ (block339S4 : ℝ) → 0 < block339V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block339RightL : ℝ) (block339RightR : ℝ) →
    y ≠ 0 → y ≠ (block339S1 : ℝ) → y ≠ (block339S2 : ℝ) →
    y ≠ (block339S3 : ℝ) → y ≠ (block339S4 : ℝ) → 0 < block339V y)

theorem block339_reallog_certificate_proof :
    block339_reallog_certificate := by
  exact ⟨block339_left_V_pos, block339_right_V_pos⟩

end Block339
end M1817475
end Erdos1038Lean
