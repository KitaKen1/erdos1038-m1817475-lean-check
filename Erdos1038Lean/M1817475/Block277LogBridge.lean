import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block277

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block277

open Set

def block277W1 : Rat := ((10288981341542343 : Rat) / 10000000000000000)
def block277W2 : Rat := ((3203751698203917 : Rat) / 100000000000000000)
def block277W3 : Rat := ((28841449033027783 : Rat) / 100000000000000000)
def block277W4 : Rat := (0 : Rat)
def block277S1 : Rat := ((18174751 : Rat) / 10000000)
def block277S2 : Rat := ((511587 : Rat) / 200000)
def block277S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block277S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block277V (y : ℝ) : ℝ :=
  ratPotential block277W1 block277W2 block277W3 block277W4 block277S1 block277S2 block277S3 block277S4 y

def block277LeftParamsCertificate : Bool :=
  allBoxesSameParams block277LeftBoxes block277W1 block277W2 block277W3 block277W4 block277S1 block277S2 block277S3 block277S4

theorem block277LeftParamsCertificate_eq_true :
    block277LeftParamsCertificate = true := by
  native_decide

theorem block277_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block277LeftL : ℝ) (block277LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block277S1 : ℝ))
    (hy2ne : y ≠ (block277S2 : ℝ))
    (hy3ne : y ≠ (block277S3 : ℝ))
    (hy4ne : y ≠ (block277S4 : ℝ)) :
    0 < block277V y := by
  have hcert := block277LeftCertificate_eq_true
  unfold block277LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block277LeftBoxes) (lo := block277LeftL) (hi := block277LeftR)
    (w1 := block277W1) (w2 := block277W2) (w3 := block277W3) (w4 := block277W4)
    (s1 := block277S1) (s2 := block277S2) (s3 := block277S3) (s4 := block277S4)
    hboxes hcover block277LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block277RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block277RightChunk000 block277W1 block277W2 block277W3 block277W4 block277S1 block277S2 block277S3 block277S4

theorem block277RightChunk000ParamsCertificate_eq_true :
    block277RightChunk000ParamsCertificate = true := by
  native_decide

theorem block277_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block277RightChunk000L : ℝ) (block277RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block277S1 : ℝ))
    (hy2ne : y ≠ (block277S2 : ℝ))
    (hy3ne : y ≠ (block277S3 : ℝ))
    (hy4ne : y ≠ (block277S4 : ℝ)) :
    0 < block277V y := by
  have hcert := block277RightChunk000Certificate_eq_true
  unfold block277RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block277RightChunk000) (lo := block277RightChunk000L) (hi := block277RightChunk000R)
    (w1 := block277W1) (w2 := block277W2) (w3 := block277W3) (w4 := block277W4)
    (s1 := block277S1) (s2 := block277S2) (s3 := block277S3) (s4 := block277S4)
    hboxes hcover block277RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block277_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block277RightL : ℝ) (block277RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block277S1 : ℝ))
    (hy2ne : y ≠ (block277S2 : ℝ))
    (hy3ne : y ≠ (block277S3 : ℝ))
    (hy4ne : y ≠ (block277S4 : ℝ)) :
    0 < block277V y := by
  have hL : (block277RightChunk000L : ℝ) = (block277RightL : ℝ) := by
    norm_num [block277RightChunk000L, block277RightL]
  have hR : (block277RightChunk000R : ℝ) = (block277RightR : ℝ) := by
    norm_num [block277RightChunk000R, block277RightR]
  have hyc : y ∈ Icc (block277RightChunk000L : ℝ) (block277RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block277_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block277_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block277LeftL : ℝ) (block277LeftR : ℝ) →
    y ≠ 0 → y ≠ (block277S1 : ℝ) → y ≠ (block277S2 : ℝ) →
    y ≠ (block277S3 : ℝ) → y ≠ (block277S4 : ℝ) → 0 < block277V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block277RightL : ℝ) (block277RightR : ℝ) →
    y ≠ 0 → y ≠ (block277S1 : ℝ) → y ≠ (block277S2 : ℝ) →
    y ≠ (block277S3 : ℝ) → y ≠ (block277S4 : ℝ) → 0 < block277V y)

theorem block277_reallog_certificate_proof :
    block277_reallog_certificate := by
  exact ⟨block277_left_V_pos, block277_right_V_pos⟩

end Block277
end M1817475
end Erdos1038Lean
