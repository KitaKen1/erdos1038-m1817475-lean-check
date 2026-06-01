import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block531

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block531

open Set

def block531W1 : Rat := ((40679046299686533 : Rat) / 100000000000000000)
def block531W2 : Rat := (0 : Rat)
def block531W3 : Rat := ((4525722803346069 : Rat) / 10000000000000000)
def block531W4 : Rat := (0 : Rat)
def block531S1 : Rat := ((18174751 : Rat) / 10000000)
def block531S2 : Rat := ((511587 : Rat) / 200000)
def block531S3 : Rat := ((129752981339285714461 : Rat) / 50000000000000000000)
def block531S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block531V (y : ℝ) : ℝ :=
  ratPotential block531W1 block531W2 block531W3 block531W4 block531S1 block531S2 block531S3 block531S4 y

def block531LeftParamsCertificate : Bool :=
  allBoxesSameParams block531LeftBoxes block531W1 block531W2 block531W3 block531W4 block531S1 block531S2 block531S3 block531S4

theorem block531LeftParamsCertificate_eq_true :
    block531LeftParamsCertificate = true := by
  native_decide

theorem block531_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block531LeftL : ℝ) (block531LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block531S1 : ℝ))
    (hy2ne : y ≠ (block531S2 : ℝ))
    (hy3ne : y ≠ (block531S3 : ℝ))
    (hy4ne : y ≠ (block531S4 : ℝ)) :
    0 < block531V y := by
  have hcert := block531LeftCertificate_eq_true
  unfold block531LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block531LeftBoxes) (lo := block531LeftL) (hi := block531LeftR)
    (w1 := block531W1) (w2 := block531W2) (w3 := block531W3) (w4 := block531W4)
    (s1 := block531S1) (s2 := block531S2) (s3 := block531S3) (s4 := block531S4)
    hboxes hcover block531LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block531RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block531RightChunk000 block531W1 block531W2 block531W3 block531W4 block531S1 block531S2 block531S3 block531S4

theorem block531RightChunk000ParamsCertificate_eq_true :
    block531RightChunk000ParamsCertificate = true := by
  native_decide

theorem block531_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block531RightChunk000L : ℝ) (block531RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block531S1 : ℝ))
    (hy2ne : y ≠ (block531S2 : ℝ))
    (hy3ne : y ≠ (block531S3 : ℝ))
    (hy4ne : y ≠ (block531S4 : ℝ)) :
    0 < block531V y := by
  have hcert := block531RightChunk000Certificate_eq_true
  unfold block531RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block531RightChunk000) (lo := block531RightChunk000L) (hi := block531RightChunk000R)
    (w1 := block531W1) (w2 := block531W2) (w3 := block531W3) (w4 := block531W4)
    (s1 := block531S1) (s2 := block531S2) (s3 := block531S3) (s4 := block531S4)
    hboxes hcover block531RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block531_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block531RightL : ℝ) (block531RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block531S1 : ℝ))
    (hy2ne : y ≠ (block531S2 : ℝ))
    (hy3ne : y ≠ (block531S3 : ℝ))
    (hy4ne : y ≠ (block531S4 : ℝ)) :
    0 < block531V y := by
  have hL : (block531RightChunk000L : ℝ) = (block531RightL : ℝ) := by
    norm_num [block531RightChunk000L, block531RightL]
  have hR : (block531RightChunk000R : ℝ) = (block531RightR : ℝ) := by
    norm_num [block531RightChunk000R, block531RightR]
  have hyc : y ∈ Icc (block531RightChunk000L : ℝ) (block531RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block531_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block531_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block531LeftL : ℝ) (block531LeftR : ℝ) →
    y ≠ 0 → y ≠ (block531S1 : ℝ) → y ≠ (block531S2 : ℝ) →
    y ≠ (block531S3 : ℝ) → y ≠ (block531S4 : ℝ) → 0 < block531V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block531RightL : ℝ) (block531RightR : ℝ) →
    y ≠ 0 → y ≠ (block531S1 : ℝ) → y ≠ (block531S2 : ℝ) →
    y ≠ (block531S3 : ℝ) → y ≠ (block531S4 : ℝ) → 0 < block531V y)

theorem block531_reallog_certificate_proof :
    block531_reallog_certificate := by
  exact ⟨block531_left_V_pos, block531_right_V_pos⟩

end Block531
end M1817475
end Erdos1038Lean
