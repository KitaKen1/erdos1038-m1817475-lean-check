import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block331

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block331

open Set

def block331W1 : Rat := ((9478190371674101 : Rat) / 10000000000000000)
def block331W2 : Rat := ((4717759522426041 : Rat) / 100000000000000000)
def block331W3 : Rat := ((717743943415349 : Rat) / 5000000000000000)
def block331W4 : Rat := ((6849016726919209 : Rat) / 50000000000000000)
def block331S1 : Rat := ((18174751 : Rat) / 10000000)
def block331S2 : Rat := ((511587 : Rat) / 200000)
def block331S3 : Rat := ((133662802767857142861 : Rat) / 50000000000000000000)
def block331S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block331V (y : ℝ) : ℝ :=
  ratPotential block331W1 block331W2 block331W3 block331W4 block331S1 block331S2 block331S3 block331S4 y

def block331LeftParamsCertificate : Bool :=
  allBoxesSameParams block331LeftBoxes block331W1 block331W2 block331W3 block331W4 block331S1 block331S2 block331S3 block331S4

theorem block331LeftParamsCertificate_eq_true :
    block331LeftParamsCertificate = true := by
  native_decide

theorem block331_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block331LeftL : ℝ) (block331LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block331S1 : ℝ))
    (hy2ne : y ≠ (block331S2 : ℝ))
    (hy3ne : y ≠ (block331S3 : ℝ))
    (hy4ne : y ≠ (block331S4 : ℝ)) :
    0 < block331V y := by
  have hcert := block331LeftCertificate_eq_true
  unfold block331LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block331LeftBoxes) (lo := block331LeftL) (hi := block331LeftR)
    (w1 := block331W1) (w2 := block331W2) (w3 := block331W3) (w4 := block331W4)
    (s1 := block331S1) (s2 := block331S2) (s3 := block331S3) (s4 := block331S4)
    hboxes hcover block331LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block331RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block331RightChunk000 block331W1 block331W2 block331W3 block331W4 block331S1 block331S2 block331S3 block331S4

theorem block331RightChunk000ParamsCertificate_eq_true :
    block331RightChunk000ParamsCertificate = true := by
  native_decide

theorem block331_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block331RightChunk000L : ℝ) (block331RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block331S1 : ℝ))
    (hy2ne : y ≠ (block331S2 : ℝ))
    (hy3ne : y ≠ (block331S3 : ℝ))
    (hy4ne : y ≠ (block331S4 : ℝ)) :
    0 < block331V y := by
  have hcert := block331RightChunk000Certificate_eq_true
  unfold block331RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block331RightChunk000) (lo := block331RightChunk000L) (hi := block331RightChunk000R)
    (w1 := block331W1) (w2 := block331W2) (w3 := block331W3) (w4 := block331W4)
    (s1 := block331S1) (s2 := block331S2) (s3 := block331S3) (s4 := block331S4)
    hboxes hcover block331RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block331_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block331RightL : ℝ) (block331RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block331S1 : ℝ))
    (hy2ne : y ≠ (block331S2 : ℝ))
    (hy3ne : y ≠ (block331S3 : ℝ))
    (hy4ne : y ≠ (block331S4 : ℝ)) :
    0 < block331V y := by
  have hL : (block331RightChunk000L : ℝ) = (block331RightL : ℝ) := by
    norm_num [block331RightChunk000L, block331RightL]
  have hR : (block331RightChunk000R : ℝ) = (block331RightR : ℝ) := by
    norm_num [block331RightChunk000R, block331RightR]
  have hyc : y ∈ Icc (block331RightChunk000L : ℝ) (block331RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block331_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block331_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block331LeftL : ℝ) (block331LeftR : ℝ) →
    y ≠ 0 → y ≠ (block331S1 : ℝ) → y ≠ (block331S2 : ℝ) →
    y ≠ (block331S3 : ℝ) → y ≠ (block331S4 : ℝ) → 0 < block331V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block331RightL : ℝ) (block331RightR : ℝ) →
    y ≠ 0 → y ≠ (block331S1 : ℝ) → y ≠ (block331S2 : ℝ) →
    y ≠ (block331S3 : ℝ) → y ≠ (block331S4 : ℝ) → 0 < block331V y)

theorem block331_reallog_certificate_proof :
    block331_reallog_certificate := by
  exact ⟨block331_left_V_pos, block331_right_V_pos⟩

end Block331
end M1817475
end Erdos1038Lean
