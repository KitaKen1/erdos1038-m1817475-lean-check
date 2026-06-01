import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block278

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block278

open Set

def block278W1 : Rat := ((10288575990239293 : Rat) / 10000000000000000)
def block278W2 : Rat := ((1623555106865563 : Rat) / 50000000000000000)
def block278W3 : Rat := ((2877498846059973 : Rat) / 10000000000000000)
def block278W4 : Rat := (0 : Rat)
def block278S1 : Rat := ((18174751 : Rat) / 10000000)
def block278S2 : Rat := ((511587 : Rat) / 200000)
def block278S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block278S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block278V (y : ℝ) : ℝ :=
  ratPotential block278W1 block278W2 block278W3 block278W4 block278S1 block278S2 block278S3 block278S4 y

def block278LeftParamsCertificate : Bool :=
  allBoxesSameParams block278LeftBoxes block278W1 block278W2 block278W3 block278W4 block278S1 block278S2 block278S3 block278S4

theorem block278LeftParamsCertificate_eq_true :
    block278LeftParamsCertificate = true := by
  native_decide

theorem block278_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block278LeftL : ℝ) (block278LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block278S1 : ℝ))
    (hy2ne : y ≠ (block278S2 : ℝ))
    (hy3ne : y ≠ (block278S3 : ℝ))
    (hy4ne : y ≠ (block278S4 : ℝ)) :
    0 < block278V y := by
  have hcert := block278LeftCertificate_eq_true
  unfold block278LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block278LeftBoxes) (lo := block278LeftL) (hi := block278LeftR)
    (w1 := block278W1) (w2 := block278W2) (w3 := block278W3) (w4 := block278W4)
    (s1 := block278S1) (s2 := block278S2) (s3 := block278S3) (s4 := block278S4)
    hboxes hcover block278LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block278RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block278RightChunk000 block278W1 block278W2 block278W3 block278W4 block278S1 block278S2 block278S3 block278S4

theorem block278RightChunk000ParamsCertificate_eq_true :
    block278RightChunk000ParamsCertificate = true := by
  native_decide

theorem block278_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block278RightChunk000L : ℝ) (block278RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block278S1 : ℝ))
    (hy2ne : y ≠ (block278S2 : ℝ))
    (hy3ne : y ≠ (block278S3 : ℝ))
    (hy4ne : y ≠ (block278S4 : ℝ)) :
    0 < block278V y := by
  have hcert := block278RightChunk000Certificate_eq_true
  unfold block278RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block278RightChunk000) (lo := block278RightChunk000L) (hi := block278RightChunk000R)
    (w1 := block278W1) (w2 := block278W2) (w3 := block278W3) (w4 := block278W4)
    (s1 := block278S1) (s2 := block278S2) (s3 := block278S3) (s4 := block278S4)
    hboxes hcover block278RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block278_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block278RightL : ℝ) (block278RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block278S1 : ℝ))
    (hy2ne : y ≠ (block278S2 : ℝ))
    (hy3ne : y ≠ (block278S3 : ℝ))
    (hy4ne : y ≠ (block278S4 : ℝ)) :
    0 < block278V y := by
  have hL : (block278RightChunk000L : ℝ) = (block278RightL : ℝ) := by
    norm_num [block278RightChunk000L, block278RightL]
  have hR : (block278RightChunk000R : ℝ) = (block278RightR : ℝ) := by
    norm_num [block278RightChunk000R, block278RightR]
  have hyc : y ∈ Icc (block278RightChunk000L : ℝ) (block278RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block278_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block278_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block278LeftL : ℝ) (block278LeftR : ℝ) →
    y ≠ 0 → y ≠ (block278S1 : ℝ) → y ≠ (block278S2 : ℝ) →
    y ≠ (block278S3 : ℝ) → y ≠ (block278S4 : ℝ) → 0 < block278V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block278RightL : ℝ) (block278RightR : ℝ) →
    y ≠ 0 → y ≠ (block278S1 : ℝ) → y ≠ (block278S2 : ℝ) →
    y ≠ (block278S3 : ℝ) → y ≠ (block278S4 : ℝ) → 0 < block278V y)

theorem block278_reallog_certificate_proof :
    block278_reallog_certificate := by
  exact ⟨block278_left_V_pos, block278_right_V_pos⟩

end Block278
end M1817475
end Erdos1038Lean
