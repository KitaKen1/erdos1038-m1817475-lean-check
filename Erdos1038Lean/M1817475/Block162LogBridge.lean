import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block162

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block162

open Set

def block162W1 : Rat := ((18545625272609727 : Rat) / 10000000000000000)
def block162W2 : Rat := (0 : Rat)
def block162W3 : Rat := ((4066781451032831 : Rat) / 25000000000000000)
def block162W4 : Rat := ((10482215133737527 : Rat) / 100000000000000000)
def block162S1 : Rat := ((18174751 : Rat) / 10000000)
def block162S2 : Rat := ((511587 : Rat) / 200000)
def block162S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block162S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block162V (y : ℝ) : ℝ :=
  ratPotential block162W1 block162W2 block162W3 block162W4 block162S1 block162S2 block162S3 block162S4 y

def block162LeftParamsCertificate : Bool :=
  allBoxesSameParams block162LeftBoxes block162W1 block162W2 block162W3 block162W4 block162S1 block162S2 block162S3 block162S4

theorem block162LeftParamsCertificate_eq_true :
    block162LeftParamsCertificate = true := by
  native_decide

theorem block162_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block162LeftL : ℝ) (block162LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block162S1 : ℝ))
    (hy2ne : y ≠ (block162S2 : ℝ))
    (hy3ne : y ≠ (block162S3 : ℝ))
    (hy4ne : y ≠ (block162S4 : ℝ)) :
    0 < block162V y := by
  have hcert := block162LeftCertificate_eq_true
  unfold block162LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block162LeftBoxes) (lo := block162LeftL) (hi := block162LeftR)
    (w1 := block162W1) (w2 := block162W2) (w3 := block162W3) (w4 := block162W4)
    (s1 := block162S1) (s2 := block162S2) (s3 := block162S3) (s4 := block162S4)
    hboxes hcover block162LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block162RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block162RightChunk000 block162W1 block162W2 block162W3 block162W4 block162S1 block162S2 block162S3 block162S4

theorem block162RightChunk000ParamsCertificate_eq_true :
    block162RightChunk000ParamsCertificate = true := by
  native_decide

theorem block162_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block162RightChunk000L : ℝ) (block162RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block162S1 : ℝ))
    (hy2ne : y ≠ (block162S2 : ℝ))
    (hy3ne : y ≠ (block162S3 : ℝ))
    (hy4ne : y ≠ (block162S4 : ℝ)) :
    0 < block162V y := by
  have hcert := block162RightChunk000Certificate_eq_true
  unfold block162RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block162RightChunk000) (lo := block162RightChunk000L) (hi := block162RightChunk000R)
    (w1 := block162W1) (w2 := block162W2) (w3 := block162W3) (w4 := block162W4)
    (s1 := block162S1) (s2 := block162S2) (s3 := block162S3) (s4 := block162S4)
    hboxes hcover block162RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block162_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block162RightL : ℝ) (block162RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block162S1 : ℝ))
    (hy2ne : y ≠ (block162S2 : ℝ))
    (hy3ne : y ≠ (block162S3 : ℝ))
    (hy4ne : y ≠ (block162S4 : ℝ)) :
    0 < block162V y := by
  have hL : (block162RightChunk000L : ℝ) = (block162RightL : ℝ) := by
    norm_num [block162RightChunk000L, block162RightL]
  have hR : (block162RightChunk000R : ℝ) = (block162RightR : ℝ) := by
    norm_num [block162RightChunk000R, block162RightR]
  have hyc : y ∈ Icc (block162RightChunk000L : ℝ) (block162RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block162_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block162_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block162LeftL : ℝ) (block162LeftR : ℝ) →
    y ≠ 0 → y ≠ (block162S1 : ℝ) → y ≠ (block162S2 : ℝ) →
    y ≠ (block162S3 : ℝ) → y ≠ (block162S4 : ℝ) → 0 < block162V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block162RightL : ℝ) (block162RightR : ℝ) →
    y ≠ 0 → y ≠ (block162S1 : ℝ) → y ≠ (block162S2 : ℝ) →
    y ≠ (block162S3 : ℝ) → y ≠ (block162S4 : ℝ) → 0 < block162V y)

theorem block162_reallog_certificate_proof :
    block162_reallog_certificate := by
  exact ⟨block162_left_V_pos, block162_right_V_pos⟩

end Block162
end M1817475
end Erdos1038Lean
