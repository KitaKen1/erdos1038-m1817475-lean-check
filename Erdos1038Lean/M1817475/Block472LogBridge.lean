import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block472

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block472

open Set

def block472W1 : Rat := ((2681419792930429 : Rat) / 5000000000000000)
def block472W2 : Rat := (0 : Rat)
def block472W3 : Rat := ((7298574377309781 : Rat) / 20000000000000000)
def block472W4 : Rat := ((3107557355865021 : Rat) / 62500000000000000)
def block472S1 : Rat := ((18174751 : Rat) / 10000000)
def block472S2 : Rat := ((511587 : Rat) / 200000)
def block472S3 : Rat := ((130906378660714285839 : Rat) / 50000000000000000000)
def block472S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block472V (y : ℝ) : ℝ :=
  ratPotential block472W1 block472W2 block472W3 block472W4 block472S1 block472S2 block472S3 block472S4 y

def block472LeftParamsCertificate : Bool :=
  allBoxesSameParams block472LeftBoxes block472W1 block472W2 block472W3 block472W4 block472S1 block472S2 block472S3 block472S4

theorem block472LeftParamsCertificate_eq_true :
    block472LeftParamsCertificate = true := by
  native_decide

theorem block472_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block472LeftL : ℝ) (block472LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block472S1 : ℝ))
    (hy2ne : y ≠ (block472S2 : ℝ))
    (hy3ne : y ≠ (block472S3 : ℝ))
    (hy4ne : y ≠ (block472S4 : ℝ)) :
    0 < block472V y := by
  have hcert := block472LeftCertificate_eq_true
  unfold block472LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block472LeftBoxes) (lo := block472LeftL) (hi := block472LeftR)
    (w1 := block472W1) (w2 := block472W2) (w3 := block472W3) (w4 := block472W4)
    (s1 := block472S1) (s2 := block472S2) (s3 := block472S3) (s4 := block472S4)
    hboxes hcover block472LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block472RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block472RightChunk000 block472W1 block472W2 block472W3 block472W4 block472S1 block472S2 block472S3 block472S4

theorem block472RightChunk000ParamsCertificate_eq_true :
    block472RightChunk000ParamsCertificate = true := by
  native_decide

theorem block472_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block472RightChunk000L : ℝ) (block472RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block472S1 : ℝ))
    (hy2ne : y ≠ (block472S2 : ℝ))
    (hy3ne : y ≠ (block472S3 : ℝ))
    (hy4ne : y ≠ (block472S4 : ℝ)) :
    0 < block472V y := by
  have hcert := block472RightChunk000Certificate_eq_true
  unfold block472RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block472RightChunk000) (lo := block472RightChunk000L) (hi := block472RightChunk000R)
    (w1 := block472W1) (w2 := block472W2) (w3 := block472W3) (w4 := block472W4)
    (s1 := block472S1) (s2 := block472S2) (s3 := block472S3) (s4 := block472S4)
    hboxes hcover block472RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block472_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block472RightL : ℝ) (block472RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block472S1 : ℝ))
    (hy2ne : y ≠ (block472S2 : ℝ))
    (hy3ne : y ≠ (block472S3 : ℝ))
    (hy4ne : y ≠ (block472S4 : ℝ)) :
    0 < block472V y := by
  have hL : (block472RightChunk000L : ℝ) = (block472RightL : ℝ) := by
    norm_num [block472RightChunk000L, block472RightL]
  have hR : (block472RightChunk000R : ℝ) = (block472RightR : ℝ) := by
    norm_num [block472RightChunk000R, block472RightR]
  have hyc : y ∈ Icc (block472RightChunk000L : ℝ) (block472RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block472_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block472_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block472LeftL : ℝ) (block472LeftR : ℝ) →
    y ≠ 0 → y ≠ (block472S1 : ℝ) → y ≠ (block472S2 : ℝ) →
    y ≠ (block472S3 : ℝ) → y ≠ (block472S4 : ℝ) → 0 < block472V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block472RightL : ℝ) (block472RightR : ℝ) →
    y ≠ 0 → y ≠ (block472S1 : ℝ) → y ≠ (block472S2 : ℝ) →
    y ≠ (block472S3 : ℝ) → y ≠ (block472S4 : ℝ) → 0 < block472V y)

theorem block472_reallog_certificate_proof :
    block472_reallog_certificate := by
  exact ⟨block472_left_V_pos, block472_right_V_pos⟩

end Block472
end M1817475
end Erdos1038Lean
