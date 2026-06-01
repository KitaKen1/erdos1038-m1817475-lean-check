import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block321

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block321

open Set

def block321W1 : Rat := ((1172807613975573 : Rat) / 1250000000000000)
def block321W2 : Rat := ((6952306777231537 : Rat) / 100000000000000000)
def block321W3 : Rat := ((1258245845224187 : Rat) / 5000000000000000)
def block321W4 : Rat := (0 : Rat)
def block321S1 : Rat := ((18174751 : Rat) / 10000000)
def block321S2 : Rat := ((511587 : Rat) / 200000)
def block321S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block321S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block321V (y : ℝ) : ℝ :=
  ratPotential block321W1 block321W2 block321W3 block321W4 block321S1 block321S2 block321S3 block321S4 y

def block321LeftParamsCertificate : Bool :=
  allBoxesSameParams block321LeftBoxes block321W1 block321W2 block321W3 block321W4 block321S1 block321S2 block321S3 block321S4

theorem block321LeftParamsCertificate_eq_true :
    block321LeftParamsCertificate = true := by
  native_decide

theorem block321_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block321LeftL : ℝ) (block321LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block321S1 : ℝ))
    (hy2ne : y ≠ (block321S2 : ℝ))
    (hy3ne : y ≠ (block321S3 : ℝ))
    (hy4ne : y ≠ (block321S4 : ℝ)) :
    0 < block321V y := by
  have hcert := block321LeftCertificate_eq_true
  unfold block321LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block321LeftBoxes) (lo := block321LeftL) (hi := block321LeftR)
    (w1 := block321W1) (w2 := block321W2) (w3 := block321W3) (w4 := block321W4)
    (s1 := block321S1) (s2 := block321S2) (s3 := block321S3) (s4 := block321S4)
    hboxes hcover block321LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block321RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block321RightChunk000 block321W1 block321W2 block321W3 block321W4 block321S1 block321S2 block321S3 block321S4

theorem block321RightChunk000ParamsCertificate_eq_true :
    block321RightChunk000ParamsCertificate = true := by
  native_decide

theorem block321_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block321RightChunk000L : ℝ) (block321RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block321S1 : ℝ))
    (hy2ne : y ≠ (block321S2 : ℝ))
    (hy3ne : y ≠ (block321S3 : ℝ))
    (hy4ne : y ≠ (block321S4 : ℝ)) :
    0 < block321V y := by
  have hcert := block321RightChunk000Certificate_eq_true
  unfold block321RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block321RightChunk000) (lo := block321RightChunk000L) (hi := block321RightChunk000R)
    (w1 := block321W1) (w2 := block321W2) (w3 := block321W3) (w4 := block321W4)
    (s1 := block321S1) (s2 := block321S2) (s3 := block321S3) (s4 := block321S4)
    hboxes hcover block321RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block321_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block321RightL : ℝ) (block321RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block321S1 : ℝ))
    (hy2ne : y ≠ (block321S2 : ℝ))
    (hy3ne : y ≠ (block321S3 : ℝ))
    (hy4ne : y ≠ (block321S4 : ℝ)) :
    0 < block321V y := by
  have hL : (block321RightChunk000L : ℝ) = (block321RightL : ℝ) := by
    norm_num [block321RightChunk000L, block321RightL]
  have hR : (block321RightChunk000R : ℝ) = (block321RightR : ℝ) := by
    norm_num [block321RightChunk000R, block321RightR]
  have hyc : y ∈ Icc (block321RightChunk000L : ℝ) (block321RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block321_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block321_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block321LeftL : ℝ) (block321LeftR : ℝ) →
    y ≠ 0 → y ≠ (block321S1 : ℝ) → y ≠ (block321S2 : ℝ) →
    y ≠ (block321S3 : ℝ) → y ≠ (block321S4 : ℝ) → 0 < block321V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block321RightL : ℝ) (block321RightR : ℝ) →
    y ≠ 0 → y ≠ (block321S1 : ℝ) → y ≠ (block321S2 : ℝ) →
    y ≠ (block321S3 : ℝ) → y ≠ (block321S4 : ℝ) → 0 < block321V y)

theorem block321_reallog_certificate_proof :
    block321_reallog_certificate := by
  exact ⟨block321_left_V_pos, block321_right_V_pos⟩

end Block321
end M1817475
end Erdos1038Lean
