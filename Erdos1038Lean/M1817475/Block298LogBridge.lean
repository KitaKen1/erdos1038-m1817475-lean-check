import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block298

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block298

open Set

def block298W1 : Rat := ((10046523321681373 : Rat) / 10000000000000000)
def block298W2 : Rat := ((4546422100586029 : Rat) / 100000000000000000)
def block298W3 : Rat := ((26630964288389 : Rat) / 97656250000000)
def block298W4 : Rat := (0 : Rat)
def block298S1 : Rat := ((18174751 : Rat) / 10000000)
def block298S2 : Rat := ((511587 : Rat) / 200000)
def block298S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block298S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block298V (y : ℝ) : ℝ :=
  ratPotential block298W1 block298W2 block298W3 block298W4 block298S1 block298S2 block298S3 block298S4 y

def block298LeftParamsCertificate : Bool :=
  allBoxesSameParams block298LeftBoxes block298W1 block298W2 block298W3 block298W4 block298S1 block298S2 block298S3 block298S4

theorem block298LeftParamsCertificate_eq_true :
    block298LeftParamsCertificate = true := by
  native_decide

theorem block298_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block298LeftL : ℝ) (block298LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block298S1 : ℝ))
    (hy2ne : y ≠ (block298S2 : ℝ))
    (hy3ne : y ≠ (block298S3 : ℝ))
    (hy4ne : y ≠ (block298S4 : ℝ)) :
    0 < block298V y := by
  have hcert := block298LeftCertificate_eq_true
  unfold block298LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block298LeftBoxes) (lo := block298LeftL) (hi := block298LeftR)
    (w1 := block298W1) (w2 := block298W2) (w3 := block298W3) (w4 := block298W4)
    (s1 := block298S1) (s2 := block298S2) (s3 := block298S3) (s4 := block298S4)
    hboxes hcover block298LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block298RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block298RightChunk000 block298W1 block298W2 block298W3 block298W4 block298S1 block298S2 block298S3 block298S4

theorem block298RightChunk000ParamsCertificate_eq_true :
    block298RightChunk000ParamsCertificate = true := by
  native_decide

theorem block298_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block298RightChunk000L : ℝ) (block298RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block298S1 : ℝ))
    (hy2ne : y ≠ (block298S2 : ℝ))
    (hy3ne : y ≠ (block298S3 : ℝ))
    (hy4ne : y ≠ (block298S4 : ℝ)) :
    0 < block298V y := by
  have hcert := block298RightChunk000Certificate_eq_true
  unfold block298RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block298RightChunk000) (lo := block298RightChunk000L) (hi := block298RightChunk000R)
    (w1 := block298W1) (w2 := block298W2) (w3 := block298W3) (w4 := block298W4)
    (s1 := block298S1) (s2 := block298S2) (s3 := block298S3) (s4 := block298S4)
    hboxes hcover block298RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block298_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block298RightL : ℝ) (block298RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block298S1 : ℝ))
    (hy2ne : y ≠ (block298S2 : ℝ))
    (hy3ne : y ≠ (block298S3 : ℝ))
    (hy4ne : y ≠ (block298S4 : ℝ)) :
    0 < block298V y := by
  have hL : (block298RightChunk000L : ℝ) = (block298RightL : ℝ) := by
    norm_num [block298RightChunk000L, block298RightL]
  have hR : (block298RightChunk000R : ℝ) = (block298RightR : ℝ) := by
    norm_num [block298RightChunk000R, block298RightR]
  have hyc : y ∈ Icc (block298RightChunk000L : ℝ) (block298RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block298_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block298_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block298LeftL : ℝ) (block298LeftR : ℝ) →
    y ≠ 0 → y ≠ (block298S1 : ℝ) → y ≠ (block298S2 : ℝ) →
    y ≠ (block298S3 : ℝ) → y ≠ (block298S4 : ℝ) → 0 < block298V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block298RightL : ℝ) (block298RightR : ℝ) →
    y ≠ 0 → y ≠ (block298S1 : ℝ) → y ≠ (block298S2 : ℝ) →
    y ≠ (block298S3 : ℝ) → y ≠ (block298S4 : ℝ) → 0 < block298V y)

theorem block298_reallog_certificate_proof :
    block298_reallog_certificate := by
  exact ⟨block298_left_V_pos, block298_right_V_pos⟩

end Block298
end M1817475
end Erdos1038Lean
