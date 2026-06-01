import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block302

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block302

open Set

def block302W1 : Rat := ((1986658904642177 : Rat) / 2000000000000000)
def block302W2 : Rat := ((12344563576176049 : Rat) / 250000000000000000)
def block302W3 : Rat := ((2691599261825117 : Rat) / 10000000000000000)
def block302W4 : Rat := (0 : Rat)
def block302S1 : Rat := ((18174751 : Rat) / 10000000)
def block302S2 : Rat := ((511587 : Rat) / 200000)
def block302S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block302S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block302V (y : ℝ) : ℝ :=
  ratPotential block302W1 block302W2 block302W3 block302W4 block302S1 block302S2 block302S3 block302S4 y

def block302LeftParamsCertificate : Bool :=
  allBoxesSameParams block302LeftBoxes block302W1 block302W2 block302W3 block302W4 block302S1 block302S2 block302S3 block302S4

theorem block302LeftParamsCertificate_eq_true :
    block302LeftParamsCertificate = true := by
  native_decide

theorem block302_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block302LeftL : ℝ) (block302LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block302S1 : ℝ))
    (hy2ne : y ≠ (block302S2 : ℝ))
    (hy3ne : y ≠ (block302S3 : ℝ))
    (hy4ne : y ≠ (block302S4 : ℝ)) :
    0 < block302V y := by
  have hcert := block302LeftCertificate_eq_true
  unfold block302LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block302LeftBoxes) (lo := block302LeftL) (hi := block302LeftR)
    (w1 := block302W1) (w2 := block302W2) (w3 := block302W3) (w4 := block302W4)
    (s1 := block302S1) (s2 := block302S2) (s3 := block302S3) (s4 := block302S4)
    hboxes hcover block302LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block302RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block302RightChunk000 block302W1 block302W2 block302W3 block302W4 block302S1 block302S2 block302S3 block302S4

theorem block302RightChunk000ParamsCertificate_eq_true :
    block302RightChunk000ParamsCertificate = true := by
  native_decide

theorem block302_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block302RightChunk000L : ℝ) (block302RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block302S1 : ℝ))
    (hy2ne : y ≠ (block302S2 : ℝ))
    (hy3ne : y ≠ (block302S3 : ℝ))
    (hy4ne : y ≠ (block302S4 : ℝ)) :
    0 < block302V y := by
  have hcert := block302RightChunk000Certificate_eq_true
  unfold block302RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block302RightChunk000) (lo := block302RightChunk000L) (hi := block302RightChunk000R)
    (w1 := block302W1) (w2 := block302W2) (w3 := block302W3) (w4 := block302W4)
    (s1 := block302S1) (s2 := block302S2) (s3 := block302S3) (s4 := block302S4)
    hboxes hcover block302RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block302_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block302RightL : ℝ) (block302RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block302S1 : ℝ))
    (hy2ne : y ≠ (block302S2 : ℝ))
    (hy3ne : y ≠ (block302S3 : ℝ))
    (hy4ne : y ≠ (block302S4 : ℝ)) :
    0 < block302V y := by
  have hL : (block302RightChunk000L : ℝ) = (block302RightL : ℝ) := by
    norm_num [block302RightChunk000L, block302RightL]
  have hR : (block302RightChunk000R : ℝ) = (block302RightR : ℝ) := by
    norm_num [block302RightChunk000R, block302RightR]
  have hyc : y ∈ Icc (block302RightChunk000L : ℝ) (block302RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block302_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block302_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block302LeftL : ℝ) (block302LeftR : ℝ) →
    y ≠ 0 → y ≠ (block302S1 : ℝ) → y ≠ (block302S2 : ℝ) →
    y ≠ (block302S3 : ℝ) → y ≠ (block302S4 : ℝ) → 0 < block302V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block302RightL : ℝ) (block302RightR : ℝ) →
    y ≠ 0 → y ≠ (block302S1 : ℝ) → y ≠ (block302S2 : ℝ) →
    y ≠ (block302S3 : ℝ) → y ≠ (block302S4 : ℝ) → 0 < block302V y)

theorem block302_reallog_certificate_proof :
    block302_reallog_certificate := by
  exact ⟨block302_left_V_pos, block302_right_V_pos⟩

end Block302
end M1817475
end Erdos1038Lean
