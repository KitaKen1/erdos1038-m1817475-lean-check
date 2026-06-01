import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block159

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block159

open Set

def block159W1 : Rat := ((9329137170905779 : Rat) / 5000000000000000)
def block159W2 : Rat := (0 : Rat)
def block159W3 : Rat := ((8044659667520661 : Rat) / 50000000000000000)
def block159W4 : Rat := ((10612044270469659 : Rat) / 100000000000000000)
def block159S1 : Rat := ((18174751 : Rat) / 10000000)
def block159S2 : Rat := ((511587 : Rat) / 200000)
def block159S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block159S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block159V (y : ℝ) : ℝ :=
  ratPotential block159W1 block159W2 block159W3 block159W4 block159S1 block159S2 block159S3 block159S4 y

def block159LeftParamsCertificate : Bool :=
  allBoxesSameParams block159LeftBoxes block159W1 block159W2 block159W3 block159W4 block159S1 block159S2 block159S3 block159S4

theorem block159LeftParamsCertificate_eq_true :
    block159LeftParamsCertificate = true := by
  native_decide

theorem block159_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block159LeftL : ℝ) (block159LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block159S1 : ℝ))
    (hy2ne : y ≠ (block159S2 : ℝ))
    (hy3ne : y ≠ (block159S3 : ℝ))
    (hy4ne : y ≠ (block159S4 : ℝ)) :
    0 < block159V y := by
  have hcert := block159LeftCertificate_eq_true
  unfold block159LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block159LeftBoxes) (lo := block159LeftL) (hi := block159LeftR)
    (w1 := block159W1) (w2 := block159W2) (w3 := block159W3) (w4 := block159W4)
    (s1 := block159S1) (s2 := block159S2) (s3 := block159S3) (s4 := block159S4)
    hboxes hcover block159LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block159RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block159RightChunk000 block159W1 block159W2 block159W3 block159W4 block159S1 block159S2 block159S3 block159S4

theorem block159RightChunk000ParamsCertificate_eq_true :
    block159RightChunk000ParamsCertificate = true := by
  native_decide

theorem block159_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block159RightChunk000L : ℝ) (block159RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block159S1 : ℝ))
    (hy2ne : y ≠ (block159S2 : ℝ))
    (hy3ne : y ≠ (block159S3 : ℝ))
    (hy4ne : y ≠ (block159S4 : ℝ)) :
    0 < block159V y := by
  have hcert := block159RightChunk000Certificate_eq_true
  unfold block159RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block159RightChunk000) (lo := block159RightChunk000L) (hi := block159RightChunk000R)
    (w1 := block159W1) (w2 := block159W2) (w3 := block159W3) (w4 := block159W4)
    (s1 := block159S1) (s2 := block159S2) (s3 := block159S3) (s4 := block159S4)
    hboxes hcover block159RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block159_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block159RightL : ℝ) (block159RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block159S1 : ℝ))
    (hy2ne : y ≠ (block159S2 : ℝ))
    (hy3ne : y ≠ (block159S3 : ℝ))
    (hy4ne : y ≠ (block159S4 : ℝ)) :
    0 < block159V y := by
  have hL : (block159RightChunk000L : ℝ) = (block159RightL : ℝ) := by
    norm_num [block159RightChunk000L, block159RightL]
  have hR : (block159RightChunk000R : ℝ) = (block159RightR : ℝ) := by
    norm_num [block159RightChunk000R, block159RightR]
  have hyc : y ∈ Icc (block159RightChunk000L : ℝ) (block159RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block159_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block159_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block159LeftL : ℝ) (block159LeftR : ℝ) →
    y ≠ 0 → y ≠ (block159S1 : ℝ) → y ≠ (block159S2 : ℝ) →
    y ≠ (block159S3 : ℝ) → y ≠ (block159S4 : ℝ) → 0 < block159V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block159RightL : ℝ) (block159RightR : ℝ) →
    y ≠ 0 → y ≠ (block159S1 : ℝ) → y ≠ (block159S2 : ℝ) →
    y ≠ (block159S3 : ℝ) → y ≠ (block159S4 : ℝ) → 0 < block159V y)

theorem block159_reallog_certificate_proof :
    block159_reallog_certificate := by
  exact ⟨block159_left_V_pos, block159_right_V_pos⟩

end Block159
end M1817475
end Erdos1038Lean
