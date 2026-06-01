import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block251

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block251

open Set

def block251W1 : Rat := ((852673330336737 : Rat) / 1000000000000000)
def block251W2 : Rat := ((885078747772891 : Rat) / 10000000000000000)
def block251W3 : Rat := ((2543848264806459 : Rat) / 50000000000000000)
def block251W4 : Rat := ((9856316473189601 : Rat) / 50000000000000000)
def block251S1 : Rat := ((18174751 : Rat) / 10000000)
def block251S2 : Rat := ((511587 : Rat) / 200000)
def block251S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block251S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block251V (y : ℝ) : ℝ :=
  ratPotential block251W1 block251W2 block251W3 block251W4 block251S1 block251S2 block251S3 block251S4 y

def block251LeftParamsCertificate : Bool :=
  allBoxesSameParams block251LeftBoxes block251W1 block251W2 block251W3 block251W4 block251S1 block251S2 block251S3 block251S4

theorem block251LeftParamsCertificate_eq_true :
    block251LeftParamsCertificate = true := by
  native_decide

theorem block251_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block251LeftL : ℝ) (block251LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block251S1 : ℝ))
    (hy2ne : y ≠ (block251S2 : ℝ))
    (hy3ne : y ≠ (block251S3 : ℝ))
    (hy4ne : y ≠ (block251S4 : ℝ)) :
    0 < block251V y := by
  have hcert := block251LeftCertificate_eq_true
  unfold block251LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block251LeftBoxes) (lo := block251LeftL) (hi := block251LeftR)
    (w1 := block251W1) (w2 := block251W2) (w3 := block251W3) (w4 := block251W4)
    (s1 := block251S1) (s2 := block251S2) (s3 := block251S3) (s4 := block251S4)
    hboxes hcover block251LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block251RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block251RightChunk000 block251W1 block251W2 block251W3 block251W4 block251S1 block251S2 block251S3 block251S4

theorem block251RightChunk000ParamsCertificate_eq_true :
    block251RightChunk000ParamsCertificate = true := by
  native_decide

theorem block251_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block251RightChunk000L : ℝ) (block251RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block251S1 : ℝ))
    (hy2ne : y ≠ (block251S2 : ℝ))
    (hy3ne : y ≠ (block251S3 : ℝ))
    (hy4ne : y ≠ (block251S4 : ℝ)) :
    0 < block251V y := by
  have hcert := block251RightChunk000Certificate_eq_true
  unfold block251RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block251RightChunk000) (lo := block251RightChunk000L) (hi := block251RightChunk000R)
    (w1 := block251W1) (w2 := block251W2) (w3 := block251W3) (w4 := block251W4)
    (s1 := block251S1) (s2 := block251S2) (s3 := block251S3) (s4 := block251S4)
    hboxes hcover block251RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block251_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block251RightL : ℝ) (block251RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block251S1 : ℝ))
    (hy2ne : y ≠ (block251S2 : ℝ))
    (hy3ne : y ≠ (block251S3 : ℝ))
    (hy4ne : y ≠ (block251S4 : ℝ)) :
    0 < block251V y := by
  have hL : (block251RightChunk000L : ℝ) = (block251RightL : ℝ) := by
    norm_num [block251RightChunk000L, block251RightL]
  have hR : (block251RightChunk000R : ℝ) = (block251RightR : ℝ) := by
    norm_num [block251RightChunk000R, block251RightR]
  have hyc : y ∈ Icc (block251RightChunk000L : ℝ) (block251RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block251_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block251_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block251LeftL : ℝ) (block251LeftR : ℝ) →
    y ≠ 0 → y ≠ (block251S1 : ℝ) → y ≠ (block251S2 : ℝ) →
    y ≠ (block251S3 : ℝ) → y ≠ (block251S4 : ℝ) → 0 < block251V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block251RightL : ℝ) (block251RightR : ℝ) →
    y ≠ 0 → y ≠ (block251S1 : ℝ) → y ≠ (block251S2 : ℝ) →
    y ≠ (block251S3 : ℝ) → y ≠ (block251S4 : ℝ) → 0 < block251V y)

theorem block251_reallog_certificate_proof :
    block251_reallog_certificate := by
  exact ⟨block251_left_V_pos, block251_right_V_pos⟩

end Block251
end M1817475
end Erdos1038Lean
