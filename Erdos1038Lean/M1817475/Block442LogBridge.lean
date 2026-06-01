import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block442

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block442

open Set

def block442W1 : Rat := ((6203747871675217 : Rat) / 10000000000000000)
def block442W2 : Rat := (0 : Rat)
def block442W3 : Rat := ((8068315318515501 : Rat) / 25000000000000000)
def block442W4 : Rat := ((362134339217963 : Rat) / 5000000000000000)
def block442S1 : Rat := ((18174751 : Rat) / 10000000)
def block442S2 : Rat := ((511587 : Rat) / 200000)
def block442S3 : Rat := ((131492851875000000099 : Rat) / 50000000000000000000)
def block442S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block442V (y : ℝ) : ℝ :=
  ratPotential block442W1 block442W2 block442W3 block442W4 block442S1 block442S2 block442S3 block442S4 y

def block442LeftParamsCertificate : Bool :=
  allBoxesSameParams block442LeftBoxes block442W1 block442W2 block442W3 block442W4 block442S1 block442S2 block442S3 block442S4

theorem block442LeftParamsCertificate_eq_true :
    block442LeftParamsCertificate = true := by
  native_decide

theorem block442_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block442LeftL : ℝ) (block442LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block442S1 : ℝ))
    (hy2ne : y ≠ (block442S2 : ℝ))
    (hy3ne : y ≠ (block442S3 : ℝ))
    (hy4ne : y ≠ (block442S4 : ℝ)) :
    0 < block442V y := by
  have hcert := block442LeftCertificate_eq_true
  unfold block442LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block442LeftBoxes) (lo := block442LeftL) (hi := block442LeftR)
    (w1 := block442W1) (w2 := block442W2) (w3 := block442W3) (w4 := block442W4)
    (s1 := block442S1) (s2 := block442S2) (s3 := block442S3) (s4 := block442S4)
    hboxes hcover block442LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block442RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block442RightChunk000 block442W1 block442W2 block442W3 block442W4 block442S1 block442S2 block442S3 block442S4

theorem block442RightChunk000ParamsCertificate_eq_true :
    block442RightChunk000ParamsCertificate = true := by
  native_decide

theorem block442_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block442RightChunk000L : ℝ) (block442RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block442S1 : ℝ))
    (hy2ne : y ≠ (block442S2 : ℝ))
    (hy3ne : y ≠ (block442S3 : ℝ))
    (hy4ne : y ≠ (block442S4 : ℝ)) :
    0 < block442V y := by
  have hcert := block442RightChunk000Certificate_eq_true
  unfold block442RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block442RightChunk000) (lo := block442RightChunk000L) (hi := block442RightChunk000R)
    (w1 := block442W1) (w2 := block442W2) (w3 := block442W3) (w4 := block442W4)
    (s1 := block442S1) (s2 := block442S2) (s3 := block442S3) (s4 := block442S4)
    hboxes hcover block442RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block442_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block442RightL : ℝ) (block442RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block442S1 : ℝ))
    (hy2ne : y ≠ (block442S2 : ℝ))
    (hy3ne : y ≠ (block442S3 : ℝ))
    (hy4ne : y ≠ (block442S4 : ℝ)) :
    0 < block442V y := by
  have hL : (block442RightChunk000L : ℝ) = (block442RightL : ℝ) := by
    norm_num [block442RightChunk000L, block442RightL]
  have hR : (block442RightChunk000R : ℝ) = (block442RightR : ℝ) := by
    norm_num [block442RightChunk000R, block442RightR]
  have hyc : y ∈ Icc (block442RightChunk000L : ℝ) (block442RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block442_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block442_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block442LeftL : ℝ) (block442LeftR : ℝ) →
    y ≠ 0 → y ≠ (block442S1 : ℝ) → y ≠ (block442S2 : ℝ) →
    y ≠ (block442S3 : ℝ) → y ≠ (block442S4 : ℝ) → 0 < block442V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block442RightL : ℝ) (block442RightR : ℝ) →
    y ≠ 0 → y ≠ (block442S1 : ℝ) → y ≠ (block442S2 : ℝ) →
    y ≠ (block442S3 : ℝ) → y ≠ (block442S4 : ℝ) → 0 < block442V y)

theorem block442_reallog_certificate_proof :
    block442_reallog_certificate := by
  exact ⟨block442_left_V_pos, block442_right_V_pos⟩

end Block442
end M1817475
end Erdos1038Lean
