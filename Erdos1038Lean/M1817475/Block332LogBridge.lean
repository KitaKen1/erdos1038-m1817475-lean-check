import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block332

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block332

open Set

def block332W1 : Rat := ((9451693809362539 : Rat) / 10000000000000000)
def block332W2 : Rat := ((4722103213713541 : Rat) / 100000000000000000)
def block332W3 : Rat := ((7200413462786287 : Rat) / 50000000000000000)
def block332W4 : Rat := ((27380479480649 : Rat) / 200000000000000)
def block332S1 : Rat := ((18174751 : Rat) / 10000000)
def block332S2 : Rat := ((511587 : Rat) / 200000)
def block332S3 : Rat := ((133643253660714285719 : Rat) / 50000000000000000000)
def block332S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block332V (y : ℝ) : ℝ :=
  ratPotential block332W1 block332W2 block332W3 block332W4 block332S1 block332S2 block332S3 block332S4 y

def block332LeftParamsCertificate : Bool :=
  allBoxesSameParams block332LeftBoxes block332W1 block332W2 block332W3 block332W4 block332S1 block332S2 block332S3 block332S4

theorem block332LeftParamsCertificate_eq_true :
    block332LeftParamsCertificate = true := by
  native_decide

theorem block332_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block332LeftL : ℝ) (block332LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block332S1 : ℝ))
    (hy2ne : y ≠ (block332S2 : ℝ))
    (hy3ne : y ≠ (block332S3 : ℝ))
    (hy4ne : y ≠ (block332S4 : ℝ)) :
    0 < block332V y := by
  have hcert := block332LeftCertificate_eq_true
  unfold block332LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block332LeftBoxes) (lo := block332LeftL) (hi := block332LeftR)
    (w1 := block332W1) (w2 := block332W2) (w3 := block332W3) (w4 := block332W4)
    (s1 := block332S1) (s2 := block332S2) (s3 := block332S3) (s4 := block332S4)
    hboxes hcover block332LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block332RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block332RightChunk000 block332W1 block332W2 block332W3 block332W4 block332S1 block332S2 block332S3 block332S4

theorem block332RightChunk000ParamsCertificate_eq_true :
    block332RightChunk000ParamsCertificate = true := by
  native_decide

theorem block332_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block332RightChunk000L : ℝ) (block332RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block332S1 : ℝ))
    (hy2ne : y ≠ (block332S2 : ℝ))
    (hy3ne : y ≠ (block332S3 : ℝ))
    (hy4ne : y ≠ (block332S4 : ℝ)) :
    0 < block332V y := by
  have hcert := block332RightChunk000Certificate_eq_true
  unfold block332RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block332RightChunk000) (lo := block332RightChunk000L) (hi := block332RightChunk000R)
    (w1 := block332W1) (w2 := block332W2) (w3 := block332W3) (w4 := block332W4)
    (s1 := block332S1) (s2 := block332S2) (s3 := block332S3) (s4 := block332S4)
    hboxes hcover block332RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block332_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block332RightL : ℝ) (block332RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block332S1 : ℝ))
    (hy2ne : y ≠ (block332S2 : ℝ))
    (hy3ne : y ≠ (block332S3 : ℝ))
    (hy4ne : y ≠ (block332S4 : ℝ)) :
    0 < block332V y := by
  have hL : (block332RightChunk000L : ℝ) = (block332RightL : ℝ) := by
    norm_num [block332RightChunk000L, block332RightL]
  have hR : (block332RightChunk000R : ℝ) = (block332RightR : ℝ) := by
    norm_num [block332RightChunk000R, block332RightR]
  have hyc : y ∈ Icc (block332RightChunk000L : ℝ) (block332RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block332_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block332_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block332LeftL : ℝ) (block332LeftR : ℝ) →
    y ≠ 0 → y ≠ (block332S1 : ℝ) → y ≠ (block332S2 : ℝ) →
    y ≠ (block332S3 : ℝ) → y ≠ (block332S4 : ℝ) → 0 < block332V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block332RightL : ℝ) (block332RightR : ℝ) →
    y ≠ 0 → y ≠ (block332S1 : ℝ) → y ≠ (block332S2 : ℝ) →
    y ≠ (block332S3 : ℝ) → y ≠ (block332S4 : ℝ) → 0 < block332V y)

theorem block332_reallog_certificate_proof :
    block332_reallog_certificate := by
  exact ⟨block332_left_V_pos, block332_right_V_pos⟩

end Block332
end M1817475
end Erdos1038Lean
