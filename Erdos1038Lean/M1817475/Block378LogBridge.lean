import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block378

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block378

open Set

def block378W1 : Rat := ((8529503642159403 : Rat) / 10000000000000000)
def block378W2 : Rat := ((2337050573264133 : Rat) / 50000000000000000)
def block378W3 : Rat := ((1574457332453511 : Rat) / 10000000000000000)
def block378W4 : Rat := ((14025114540471553 : Rat) / 100000000000000000)
def block378S1 : Rat := ((18174751 : Rat) / 10000000)
def block378S2 : Rat := ((511587 : Rat) / 200000)
def block378S3 : Rat := ((132743994732142857187 : Rat) / 50000000000000000000)
def block378S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block378V (y : ℝ) : ℝ :=
  ratPotential block378W1 block378W2 block378W3 block378W4 block378S1 block378S2 block378S3 block378S4 y

def block378LeftParamsCertificate : Bool :=
  allBoxesSameParams block378LeftBoxes block378W1 block378W2 block378W3 block378W4 block378S1 block378S2 block378S3 block378S4

theorem block378LeftParamsCertificate_eq_true :
    block378LeftParamsCertificate = true := by
  native_decide

theorem block378_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block378LeftL : ℝ) (block378LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block378S1 : ℝ))
    (hy2ne : y ≠ (block378S2 : ℝ))
    (hy3ne : y ≠ (block378S3 : ℝ))
    (hy4ne : y ≠ (block378S4 : ℝ)) :
    0 < block378V y := by
  have hcert := block378LeftCertificate_eq_true
  unfold block378LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block378LeftBoxes) (lo := block378LeftL) (hi := block378LeftR)
    (w1 := block378W1) (w2 := block378W2) (w3 := block378W3) (w4 := block378W4)
    (s1 := block378S1) (s2 := block378S2) (s3 := block378S3) (s4 := block378S4)
    hboxes hcover block378LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block378RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block378RightChunk000 block378W1 block378W2 block378W3 block378W4 block378S1 block378S2 block378S3 block378S4

theorem block378RightChunk000ParamsCertificate_eq_true :
    block378RightChunk000ParamsCertificate = true := by
  native_decide

theorem block378_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block378RightChunk000L : ℝ) (block378RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block378S1 : ℝ))
    (hy2ne : y ≠ (block378S2 : ℝ))
    (hy3ne : y ≠ (block378S3 : ℝ))
    (hy4ne : y ≠ (block378S4 : ℝ)) :
    0 < block378V y := by
  have hcert := block378RightChunk000Certificate_eq_true
  unfold block378RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block378RightChunk000) (lo := block378RightChunk000L) (hi := block378RightChunk000R)
    (w1 := block378W1) (w2 := block378W2) (w3 := block378W3) (w4 := block378W4)
    (s1 := block378S1) (s2 := block378S2) (s3 := block378S3) (s4 := block378S4)
    hboxes hcover block378RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block378_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block378RightL : ℝ) (block378RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block378S1 : ℝ))
    (hy2ne : y ≠ (block378S2 : ℝ))
    (hy3ne : y ≠ (block378S3 : ℝ))
    (hy4ne : y ≠ (block378S4 : ℝ)) :
    0 < block378V y := by
  have hL : (block378RightChunk000L : ℝ) = (block378RightL : ℝ) := by
    norm_num [block378RightChunk000L, block378RightL]
  have hR : (block378RightChunk000R : ℝ) = (block378RightR : ℝ) := by
    norm_num [block378RightChunk000R, block378RightR]
  have hyc : y ∈ Icc (block378RightChunk000L : ℝ) (block378RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block378_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block378_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block378LeftL : ℝ) (block378LeftR : ℝ) →
    y ≠ 0 → y ≠ (block378S1 : ℝ) → y ≠ (block378S2 : ℝ) →
    y ≠ (block378S3 : ℝ) → y ≠ (block378S4 : ℝ) → 0 < block378V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block378RightL : ℝ) (block378RightR : ℝ) →
    y ≠ 0 → y ≠ (block378S1 : ℝ) → y ≠ (block378S2 : ℝ) →
    y ≠ (block378S3 : ℝ) → y ≠ (block378S4 : ℝ) → 0 < block378V y)

theorem block378_reallog_certificate_proof :
    block378_reallog_certificate := by
  exact ⟨block378_left_V_pos, block378_right_V_pos⟩

end Block378
end M1817475
end Erdos1038Lean
