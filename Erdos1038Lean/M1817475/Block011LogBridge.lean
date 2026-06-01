import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block011

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block011

open Set

def block011W1 : Rat := ((578662397335841 : Rat) / 62500000000000)
def block011W2 : Rat := (0 : Rat)
def block011W3 : Rat := (0 : Rat)
def block011W4 : Rat := ((126624342640707 : Rat) / 500000000000000)
def block011S1 : Rat := ((18174751 : Rat) / 10000000)
def block011S2 : Rat := ((511587 : Rat) / 200000)
def block011S3 : Rat := ((107000619 : Rat) / 40000000)
def block011S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block011V (y : ℝ) : ℝ :=
  ratPotential block011W1 block011W2 block011W3 block011W4 block011S1 block011S2 block011S3 block011S4 y

def block011LeftParamsCertificate : Bool :=
  allBoxesSameParams block011LeftBoxes block011W1 block011W2 block011W3 block011W4 block011S1 block011S2 block011S3 block011S4

theorem block011LeftParamsCertificate_eq_true :
    block011LeftParamsCertificate = true := by
  native_decide

theorem block011_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block011LeftL : ℝ) (block011LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block011S1 : ℝ))
    (hy2ne : y ≠ (block011S2 : ℝ))
    (hy3ne : y ≠ (block011S3 : ℝ))
    (hy4ne : y ≠ (block011S4 : ℝ)) :
    0 < block011V y := by
  have hcert := block011LeftCertificate_eq_true
  unfold block011LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block011LeftBoxes) (lo := block011LeftL) (hi := block011LeftR)
    (w1 := block011W1) (w2 := block011W2) (w3 := block011W3) (w4 := block011W4)
    (s1 := block011S1) (s2 := block011S2) (s3 := block011S3) (s4 := block011S4)
    hboxes hcover block011LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block011RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block011RightChunk000 block011W1 block011W2 block011W3 block011W4 block011S1 block011S2 block011S3 block011S4

theorem block011RightChunk000ParamsCertificate_eq_true :
    block011RightChunk000ParamsCertificate = true := by
  native_decide

theorem block011_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block011RightChunk000L : ℝ) (block011RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block011S1 : ℝ))
    (hy2ne : y ≠ (block011S2 : ℝ))
    (hy3ne : y ≠ (block011S3 : ℝ))
    (hy4ne : y ≠ (block011S4 : ℝ)) :
    0 < block011V y := by
  have hcert := block011RightChunk000Certificate_eq_true
  unfold block011RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block011RightChunk000) (lo := block011RightChunk000L) (hi := block011RightChunk000R)
    (w1 := block011W1) (w2 := block011W2) (w3 := block011W3) (w4 := block011W4)
    (s1 := block011S1) (s2 := block011S2) (s3 := block011S3) (s4 := block011S4)
    hboxes hcover block011RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block011_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block011RightL : ℝ) (block011RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block011S1 : ℝ))
    (hy2ne : y ≠ (block011S2 : ℝ))
    (hy3ne : y ≠ (block011S3 : ℝ))
    (hy4ne : y ≠ (block011S4 : ℝ)) :
    0 < block011V y := by
  have hL : (block011RightChunk000L : ℝ) = (block011RightL : ℝ) := by
    norm_num [block011RightChunk000L, block011RightL]
  have hR : (block011RightChunk000R : ℝ) = (block011RightR : ℝ) := by
    norm_num [block011RightChunk000R, block011RightR]
  have hyc : y ∈ Icc (block011RightChunk000L : ℝ) (block011RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block011_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block011_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block011LeftL : ℝ) (block011LeftR : ℝ) →
    y ≠ 0 → y ≠ (block011S1 : ℝ) → y ≠ (block011S2 : ℝ) →
    y ≠ (block011S3 : ℝ) → y ≠ (block011S4 : ℝ) → 0 < block011V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block011RightL : ℝ) (block011RightR : ℝ) →
    y ≠ 0 → y ≠ (block011S1 : ℝ) → y ≠ (block011S2 : ℝ) →
    y ≠ (block011S3 : ℝ) → y ≠ (block011S4 : ℝ) → 0 < block011V y)

theorem block011_reallog_certificate_proof :
    block011_reallog_certificate := by
  exact ⟨block011_left_V_pos, block011_right_V_pos⟩

end Block011
end M1817475
end Erdos1038Lean
