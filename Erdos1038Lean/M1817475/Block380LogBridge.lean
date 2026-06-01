import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block380

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block380

open Set

def block380W1 : Rat := ((4247620513445443 : Rat) / 5000000000000000)
def block380W2 : Rat := ((4656065231455831 : Rat) / 100000000000000000)
def block380W3 : Rat := ((988605701693307 : Rat) / 6250000000000000)
def block380W4 : Rat := ((2807137195275069 : Rat) / 20000000000000000)
def block380S1 : Rat := ((18174751 : Rat) / 10000000)
def block380S2 : Rat := ((511587 : Rat) / 200000)
def block380S3 : Rat := ((132704896517857142903 : Rat) / 50000000000000000000)
def block380S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block380V (y : ℝ) : ℝ :=
  ratPotential block380W1 block380W2 block380W3 block380W4 block380S1 block380S2 block380S3 block380S4 y

def block380LeftParamsCertificate : Bool :=
  allBoxesSameParams block380LeftBoxes block380W1 block380W2 block380W3 block380W4 block380S1 block380S2 block380S3 block380S4

theorem block380LeftParamsCertificate_eq_true :
    block380LeftParamsCertificate = true := by
  native_decide

theorem block380_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block380LeftL : ℝ) (block380LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block380S1 : ℝ))
    (hy2ne : y ≠ (block380S2 : ℝ))
    (hy3ne : y ≠ (block380S3 : ℝ))
    (hy4ne : y ≠ (block380S4 : ℝ)) :
    0 < block380V y := by
  have hcert := block380LeftCertificate_eq_true
  unfold block380LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block380LeftBoxes) (lo := block380LeftL) (hi := block380LeftR)
    (w1 := block380W1) (w2 := block380W2) (w3 := block380W3) (w4 := block380W4)
    (s1 := block380S1) (s2 := block380S2) (s3 := block380S3) (s4 := block380S4)
    hboxes hcover block380LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block380RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block380RightChunk000 block380W1 block380W2 block380W3 block380W4 block380S1 block380S2 block380S3 block380S4

theorem block380RightChunk000ParamsCertificate_eq_true :
    block380RightChunk000ParamsCertificate = true := by
  native_decide

theorem block380_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block380RightChunk000L : ℝ) (block380RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block380S1 : ℝ))
    (hy2ne : y ≠ (block380S2 : ℝ))
    (hy3ne : y ≠ (block380S3 : ℝ))
    (hy4ne : y ≠ (block380S4 : ℝ)) :
    0 < block380V y := by
  have hcert := block380RightChunk000Certificate_eq_true
  unfold block380RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block380RightChunk000) (lo := block380RightChunk000L) (hi := block380RightChunk000R)
    (w1 := block380W1) (w2 := block380W2) (w3 := block380W3) (w4 := block380W4)
    (s1 := block380S1) (s2 := block380S2) (s3 := block380S3) (s4 := block380S4)
    hboxes hcover block380RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block380_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block380RightL : ℝ) (block380RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block380S1 : ℝ))
    (hy2ne : y ≠ (block380S2 : ℝ))
    (hy3ne : y ≠ (block380S3 : ℝ))
    (hy4ne : y ≠ (block380S4 : ℝ)) :
    0 < block380V y := by
  have hL : (block380RightChunk000L : ℝ) = (block380RightL : ℝ) := by
    norm_num [block380RightChunk000L, block380RightL]
  have hR : (block380RightChunk000R : ℝ) = (block380RightR : ℝ) := by
    norm_num [block380RightChunk000R, block380RightR]
  have hyc : y ∈ Icc (block380RightChunk000L : ℝ) (block380RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block380_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block380_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block380LeftL : ℝ) (block380LeftR : ℝ) →
    y ≠ 0 → y ≠ (block380S1 : ℝ) → y ≠ (block380S2 : ℝ) →
    y ≠ (block380S3 : ℝ) → y ≠ (block380S4 : ℝ) → 0 < block380V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block380RightL : ℝ) (block380RightR : ℝ) →
    y ≠ 0 → y ≠ (block380S1 : ℝ) → y ≠ (block380S2 : ℝ) →
    y ≠ (block380S3 : ℝ) → y ≠ (block380S4 : ℝ) → 0 < block380V y)

theorem block380_reallog_certificate_proof :
    block380_reallog_certificate := by
  exact ⟨block380_left_V_pos, block380_right_V_pos⟩

end Block380
end M1817475
end Erdos1038Lean
