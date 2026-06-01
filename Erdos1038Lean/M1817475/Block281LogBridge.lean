import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block281

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block281

open Set

def block281W1 : Rat := ((128575004724283 : Rat) / 125000000000000)
def block281W2 : Rat := ((3379933714280111 : Rat) / 100000000000000000)
def block281W3 : Rat := ((89294771204141 : Rat) / 312500000000000)
def block281W4 : Rat := (0 : Rat)
def block281S1 : Rat := ((18174751 : Rat) / 10000000)
def block281S2 : Rat := ((511587 : Rat) / 200000)
def block281S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block281S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block281V (y : ℝ) : ℝ :=
  ratPotential block281W1 block281W2 block281W3 block281W4 block281S1 block281S2 block281S3 block281S4 y

def block281LeftParamsCertificate : Bool :=
  allBoxesSameParams block281LeftBoxes block281W1 block281W2 block281W3 block281W4 block281S1 block281S2 block281S3 block281S4

theorem block281LeftParamsCertificate_eq_true :
    block281LeftParamsCertificate = true := by
  native_decide

theorem block281_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block281LeftL : ℝ) (block281LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block281S1 : ℝ))
    (hy2ne : y ≠ (block281S2 : ℝ))
    (hy3ne : y ≠ (block281S3 : ℝ))
    (hy4ne : y ≠ (block281S4 : ℝ)) :
    0 < block281V y := by
  have hcert := block281LeftCertificate_eq_true
  unfold block281LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block281LeftBoxes) (lo := block281LeftL) (hi := block281LeftR)
    (w1 := block281W1) (w2 := block281W2) (w3 := block281W3) (w4 := block281W4)
    (s1 := block281S1) (s2 := block281S2) (s3 := block281S3) (s4 := block281S4)
    hboxes hcover block281LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block281RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block281RightChunk000 block281W1 block281W2 block281W3 block281W4 block281S1 block281S2 block281S3 block281S4

theorem block281RightChunk000ParamsCertificate_eq_true :
    block281RightChunk000ParamsCertificate = true := by
  native_decide

theorem block281_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block281RightChunk000L : ℝ) (block281RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block281S1 : ℝ))
    (hy2ne : y ≠ (block281S2 : ℝ))
    (hy3ne : y ≠ (block281S3 : ℝ))
    (hy4ne : y ≠ (block281S4 : ℝ)) :
    0 < block281V y := by
  have hcert := block281RightChunk000Certificate_eq_true
  unfold block281RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block281RightChunk000) (lo := block281RightChunk000L) (hi := block281RightChunk000R)
    (w1 := block281W1) (w2 := block281W2) (w3 := block281W3) (w4 := block281W4)
    (s1 := block281S1) (s2 := block281S2) (s3 := block281S3) (s4 := block281S4)
    hboxes hcover block281RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block281_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block281RightL : ℝ) (block281RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block281S1 : ℝ))
    (hy2ne : y ≠ (block281S2 : ℝ))
    (hy3ne : y ≠ (block281S3 : ℝ))
    (hy4ne : y ≠ (block281S4 : ℝ)) :
    0 < block281V y := by
  have hL : (block281RightChunk000L : ℝ) = (block281RightL : ℝ) := by
    norm_num [block281RightChunk000L, block281RightL]
  have hR : (block281RightChunk000R : ℝ) = (block281RightR : ℝ) := by
    norm_num [block281RightChunk000R, block281RightR]
  have hyc : y ∈ Icc (block281RightChunk000L : ℝ) (block281RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block281_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block281_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block281LeftL : ℝ) (block281LeftR : ℝ) →
    y ≠ 0 → y ≠ (block281S1 : ℝ) → y ≠ (block281S2 : ℝ) →
    y ≠ (block281S3 : ℝ) → y ≠ (block281S4 : ℝ) → 0 < block281V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block281RightL : ℝ) (block281RightR : ℝ) →
    y ≠ 0 → y ≠ (block281S1 : ℝ) → y ≠ (block281S2 : ℝ) →
    y ≠ (block281S3 : ℝ) → y ≠ (block281S4 : ℝ) → 0 < block281V y)

theorem block281_reallog_certificate_proof :
    block281_reallog_certificate := by
  exact ⟨block281_left_V_pos, block281_right_V_pos⟩

end Block281
end M1817475
end Erdos1038Lean
