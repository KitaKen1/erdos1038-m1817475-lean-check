import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block297

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block297

open Set

def block297W1 : Rat := ((5037343253966663 : Rat) / 5000000000000000)
def block297W2 : Rat := ((4450298804305717 : Rat) / 100000000000000000)
def block297W3 : Rat := ((5471571592499097 : Rat) / 20000000000000000)
def block297W4 : Rat := (0 : Rat)
def block297S1 : Rat := ((18174751 : Rat) / 10000000)
def block297S2 : Rat := ((511587 : Rat) / 200000)
def block297S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block297S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block297V (y : ℝ) : ℝ :=
  ratPotential block297W1 block297W2 block297W3 block297W4 block297S1 block297S2 block297S3 block297S4 y

def block297LeftParamsCertificate : Bool :=
  allBoxesSameParams block297LeftBoxes block297W1 block297W2 block297W3 block297W4 block297S1 block297S2 block297S3 block297S4

theorem block297LeftParamsCertificate_eq_true :
    block297LeftParamsCertificate = true := by
  native_decide

theorem block297_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block297LeftL : ℝ) (block297LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block297S1 : ℝ))
    (hy2ne : y ≠ (block297S2 : ℝ))
    (hy3ne : y ≠ (block297S3 : ℝ))
    (hy4ne : y ≠ (block297S4 : ℝ)) :
    0 < block297V y := by
  have hcert := block297LeftCertificate_eq_true
  unfold block297LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block297LeftBoxes) (lo := block297LeftL) (hi := block297LeftR)
    (w1 := block297W1) (w2 := block297W2) (w3 := block297W3) (w4 := block297W4)
    (s1 := block297S1) (s2 := block297S2) (s3 := block297S3) (s4 := block297S4)
    hboxes hcover block297LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block297RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block297RightChunk000 block297W1 block297W2 block297W3 block297W4 block297S1 block297S2 block297S3 block297S4

theorem block297RightChunk000ParamsCertificate_eq_true :
    block297RightChunk000ParamsCertificate = true := by
  native_decide

theorem block297_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block297RightChunk000L : ℝ) (block297RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block297S1 : ℝ))
    (hy2ne : y ≠ (block297S2 : ℝ))
    (hy3ne : y ≠ (block297S3 : ℝ))
    (hy4ne : y ≠ (block297S4 : ℝ)) :
    0 < block297V y := by
  have hcert := block297RightChunk000Certificate_eq_true
  unfold block297RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block297RightChunk000) (lo := block297RightChunk000L) (hi := block297RightChunk000R)
    (w1 := block297W1) (w2 := block297W2) (w3 := block297W3) (w4 := block297W4)
    (s1 := block297S1) (s2 := block297S2) (s3 := block297S3) (s4 := block297S4)
    hboxes hcover block297RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block297_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block297RightL : ℝ) (block297RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block297S1 : ℝ))
    (hy2ne : y ≠ (block297S2 : ℝ))
    (hy3ne : y ≠ (block297S3 : ℝ))
    (hy4ne : y ≠ (block297S4 : ℝ)) :
    0 < block297V y := by
  have hL : (block297RightChunk000L : ℝ) = (block297RightL : ℝ) := by
    norm_num [block297RightChunk000L, block297RightL]
  have hR : (block297RightChunk000R : ℝ) = (block297RightR : ℝ) := by
    norm_num [block297RightChunk000R, block297RightR]
  have hyc : y ∈ Icc (block297RightChunk000L : ℝ) (block297RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block297_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block297_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block297LeftL : ℝ) (block297LeftR : ℝ) →
    y ≠ 0 → y ≠ (block297S1 : ℝ) → y ≠ (block297S2 : ℝ) →
    y ≠ (block297S3 : ℝ) → y ≠ (block297S4 : ℝ) → 0 < block297V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block297RightL : ℝ) (block297RightR : ℝ) →
    y ≠ 0 → y ≠ (block297S1 : ℝ) → y ≠ (block297S2 : ℝ) →
    y ≠ (block297S3 : ℝ) → y ≠ (block297S4 : ℝ) → 0 < block297V y)

theorem block297_reallog_certificate_proof :
    block297_reallog_certificate := by
  exact ⟨block297_left_V_pos, block297_right_V_pos⟩

end Block297
end M1817475
end Erdos1038Lean
