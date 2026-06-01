import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block283

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block283

open Set

def block283W1 : Rat := ((10286311439034657 : Rat) / 10000000000000000)
def block283W2 : Rat := ((866379398020797 : Rat) / 25000000000000000)
def block283W3 : Rat := ((355519304506361 : Rat) / 1250000000000000)
def block283W4 : Rat := (0 : Rat)
def block283S1 : Rat := ((18174751 : Rat) / 10000000)
def block283S2 : Rat := ((511587 : Rat) / 200000)
def block283S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block283S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block283V (y : ℝ) : ℝ :=
  ratPotential block283W1 block283W2 block283W3 block283W4 block283S1 block283S2 block283S3 block283S4 y

def block283LeftParamsCertificate : Bool :=
  allBoxesSameParams block283LeftBoxes block283W1 block283W2 block283W3 block283W4 block283S1 block283S2 block283S3 block283S4

theorem block283LeftParamsCertificate_eq_true :
    block283LeftParamsCertificate = true := by
  native_decide

theorem block283_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block283LeftL : ℝ) (block283LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block283S1 : ℝ))
    (hy2ne : y ≠ (block283S2 : ℝ))
    (hy3ne : y ≠ (block283S3 : ℝ))
    (hy4ne : y ≠ (block283S4 : ℝ)) :
    0 < block283V y := by
  have hcert := block283LeftCertificate_eq_true
  unfold block283LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block283LeftBoxes) (lo := block283LeftL) (hi := block283LeftR)
    (w1 := block283W1) (w2 := block283W2) (w3 := block283W3) (w4 := block283W4)
    (s1 := block283S1) (s2 := block283S2) (s3 := block283S3) (s4 := block283S4)
    hboxes hcover block283LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block283RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block283RightChunk000 block283W1 block283W2 block283W3 block283W4 block283S1 block283S2 block283S3 block283S4

theorem block283RightChunk000ParamsCertificate_eq_true :
    block283RightChunk000ParamsCertificate = true := by
  native_decide

theorem block283_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block283RightChunk000L : ℝ) (block283RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block283S1 : ℝ))
    (hy2ne : y ≠ (block283S2 : ℝ))
    (hy3ne : y ≠ (block283S3 : ℝ))
    (hy4ne : y ≠ (block283S4 : ℝ)) :
    0 < block283V y := by
  have hcert := block283RightChunk000Certificate_eq_true
  unfold block283RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block283RightChunk000) (lo := block283RightChunk000L) (hi := block283RightChunk000R)
    (w1 := block283W1) (w2 := block283W2) (w3 := block283W3) (w4 := block283W4)
    (s1 := block283S1) (s2 := block283S2) (s3 := block283S3) (s4 := block283S4)
    hboxes hcover block283RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block283_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block283RightL : ℝ) (block283RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block283S1 : ℝ))
    (hy2ne : y ≠ (block283S2 : ℝ))
    (hy3ne : y ≠ (block283S3 : ℝ))
    (hy4ne : y ≠ (block283S4 : ℝ)) :
    0 < block283V y := by
  have hL : (block283RightChunk000L : ℝ) = (block283RightL : ℝ) := by
    norm_num [block283RightChunk000L, block283RightL]
  have hR : (block283RightChunk000R : ℝ) = (block283RightR : ℝ) := by
    norm_num [block283RightChunk000R, block283RightR]
  have hyc : y ∈ Icc (block283RightChunk000L : ℝ) (block283RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block283_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block283_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block283LeftL : ℝ) (block283LeftR : ℝ) →
    y ≠ 0 → y ≠ (block283S1 : ℝ) → y ≠ (block283S2 : ℝ) →
    y ≠ (block283S3 : ℝ) → y ≠ (block283S4 : ℝ) → 0 < block283V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block283RightL : ℝ) (block283RightR : ℝ) →
    y ≠ 0 → y ≠ (block283S1 : ℝ) → y ≠ (block283S2 : ℝ) →
    y ≠ (block283S3 : ℝ) → y ≠ (block283S4 : ℝ) → 0 < block283V y)

theorem block283_reallog_certificate_proof :
    block283_reallog_certificate := by
  exact ⟨block283_left_V_pos, block283_right_V_pos⟩

end Block283
end M1817475
end Erdos1038Lean
