import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block046

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block046

open Set

def block046W1 : Rat := ((407916233677049 : Rat) / 156250000000000)
def block046W2 : Rat := (0 : Rat)
def block046W3 : Rat := (0 : Rat)
def block046W4 : Rat := ((27158514542355133 : Rat) / 100000000000000000)
def block046S1 : Rat := ((18174751 : Rat) / 10000000)
def block046S2 : Rat := ((511587 : Rat) / 200000)
def block046S3 : Rat := ((107000619 : Rat) / 40000000)
def block046S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block046V (y : ℝ) : ℝ :=
  ratPotential block046W1 block046W2 block046W3 block046W4 block046S1 block046S2 block046S3 block046S4 y

def block046LeftParamsCertificate : Bool :=
  allBoxesSameParams block046LeftBoxes block046W1 block046W2 block046W3 block046W4 block046S1 block046S2 block046S3 block046S4

theorem block046LeftParamsCertificate_eq_true :
    block046LeftParamsCertificate = true := by
  native_decide

theorem block046_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block046LeftL : ℝ) (block046LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block046S1 : ℝ))
    (hy2ne : y ≠ (block046S2 : ℝ))
    (hy3ne : y ≠ (block046S3 : ℝ))
    (hy4ne : y ≠ (block046S4 : ℝ)) :
    0 < block046V y := by
  have hcert := block046LeftCertificate_eq_true
  unfold block046LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block046LeftBoxes) (lo := block046LeftL) (hi := block046LeftR)
    (w1 := block046W1) (w2 := block046W2) (w3 := block046W3) (w4 := block046W4)
    (s1 := block046S1) (s2 := block046S2) (s3 := block046S3) (s4 := block046S4)
    hboxes hcover block046LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block046RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block046RightChunk000 block046W1 block046W2 block046W3 block046W4 block046S1 block046S2 block046S3 block046S4

theorem block046RightChunk000ParamsCertificate_eq_true :
    block046RightChunk000ParamsCertificate = true := by
  native_decide

theorem block046_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block046RightChunk000L : ℝ) (block046RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block046S1 : ℝ))
    (hy2ne : y ≠ (block046S2 : ℝ))
    (hy3ne : y ≠ (block046S3 : ℝ))
    (hy4ne : y ≠ (block046S4 : ℝ)) :
    0 < block046V y := by
  have hcert := block046RightChunk000Certificate_eq_true
  unfold block046RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block046RightChunk000) (lo := block046RightChunk000L) (hi := block046RightChunk000R)
    (w1 := block046W1) (w2 := block046W2) (w3 := block046W3) (w4 := block046W4)
    (s1 := block046S1) (s2 := block046S2) (s3 := block046S3) (s4 := block046S4)
    hboxes hcover block046RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block046_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block046RightL : ℝ) (block046RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block046S1 : ℝ))
    (hy2ne : y ≠ (block046S2 : ℝ))
    (hy3ne : y ≠ (block046S3 : ℝ))
    (hy4ne : y ≠ (block046S4 : ℝ)) :
    0 < block046V y := by
  have hL : (block046RightChunk000L : ℝ) = (block046RightL : ℝ) := by
    norm_num [block046RightChunk000L, block046RightL]
  have hR : (block046RightChunk000R : ℝ) = (block046RightR : ℝ) := by
    norm_num [block046RightChunk000R, block046RightR]
  have hyc : y ∈ Icc (block046RightChunk000L : ℝ) (block046RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block046_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block046_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block046LeftL : ℝ) (block046LeftR : ℝ) →
    y ≠ 0 → y ≠ (block046S1 : ℝ) → y ≠ (block046S2 : ℝ) →
    y ≠ (block046S3 : ℝ) → y ≠ (block046S4 : ℝ) → 0 < block046V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block046RightL : ℝ) (block046RightR : ℝ) →
    y ≠ 0 → y ≠ (block046S1 : ℝ) → y ≠ (block046S2 : ℝ) →
    y ≠ (block046S3 : ℝ) → y ≠ (block046S4 : ℝ) → 0 < block046V y)

theorem block046_reallog_certificate_proof :
    block046_reallog_certificate := by
  exact ⟨block046_left_V_pos, block046_right_V_pos⟩

end Block046
end M1817475
end Erdos1038Lean
