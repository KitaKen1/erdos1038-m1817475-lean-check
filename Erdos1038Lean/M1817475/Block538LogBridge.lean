import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block538

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block538

open Set

def block538W1 : Rat := ((19982276344919517 : Rat) / 50000000000000000)
def block538W2 : Rat := (0 : Rat)
def block538W3 : Rat := ((4552319411973431 : Rat) / 10000000000000000)
def block538W4 : Rat := (0 : Rat)
def block538S1 : Rat := ((18174751 : Rat) / 10000000)
def block538S2 : Rat := ((511587 : Rat) / 200000)
def block538S3 : Rat := ((129616137589285714467 : Rat) / 50000000000000000000)
def block538S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block538V (y : ℝ) : ℝ :=
  ratPotential block538W1 block538W2 block538W3 block538W4 block538S1 block538S2 block538S3 block538S4 y

def block538LeftParamsCertificate : Bool :=
  allBoxesSameParams block538LeftBoxes block538W1 block538W2 block538W3 block538W4 block538S1 block538S2 block538S3 block538S4

theorem block538LeftParamsCertificate_eq_true :
    block538LeftParamsCertificate = true := by
  native_decide

theorem block538_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block538LeftL : ℝ) (block538LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block538S1 : ℝ))
    (hy2ne : y ≠ (block538S2 : ℝ))
    (hy3ne : y ≠ (block538S3 : ℝ))
    (hy4ne : y ≠ (block538S4 : ℝ)) :
    0 < block538V y := by
  have hcert := block538LeftCertificate_eq_true
  unfold block538LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block538LeftBoxes) (lo := block538LeftL) (hi := block538LeftR)
    (w1 := block538W1) (w2 := block538W2) (w3 := block538W3) (w4 := block538W4)
    (s1 := block538S1) (s2 := block538S2) (s3 := block538S3) (s4 := block538S4)
    hboxes hcover block538LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block538RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block538RightChunk000 block538W1 block538W2 block538W3 block538W4 block538S1 block538S2 block538S3 block538S4

theorem block538RightChunk000ParamsCertificate_eq_true :
    block538RightChunk000ParamsCertificate = true := by
  native_decide

theorem block538_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block538RightChunk000L : ℝ) (block538RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block538S1 : ℝ))
    (hy2ne : y ≠ (block538S2 : ℝ))
    (hy3ne : y ≠ (block538S3 : ℝ))
    (hy4ne : y ≠ (block538S4 : ℝ)) :
    0 < block538V y := by
  have hcert := block538RightChunk000Certificate_eq_true
  unfold block538RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block538RightChunk000) (lo := block538RightChunk000L) (hi := block538RightChunk000R)
    (w1 := block538W1) (w2 := block538W2) (w3 := block538W3) (w4 := block538W4)
    (s1 := block538S1) (s2 := block538S2) (s3 := block538S3) (s4 := block538S4)
    hboxes hcover block538RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block538_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block538RightL : ℝ) (block538RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block538S1 : ℝ))
    (hy2ne : y ≠ (block538S2 : ℝ))
    (hy3ne : y ≠ (block538S3 : ℝ))
    (hy4ne : y ≠ (block538S4 : ℝ)) :
    0 < block538V y := by
  have hL : (block538RightChunk000L : ℝ) = (block538RightL : ℝ) := by
    norm_num [block538RightChunk000L, block538RightL]
  have hR : (block538RightChunk000R : ℝ) = (block538RightR : ℝ) := by
    norm_num [block538RightChunk000R, block538RightR]
  have hyc : y ∈ Icc (block538RightChunk000L : ℝ) (block538RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block538_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block538_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block538LeftL : ℝ) (block538LeftR : ℝ) →
    y ≠ 0 → y ≠ (block538S1 : ℝ) → y ≠ (block538S2 : ℝ) →
    y ≠ (block538S3 : ℝ) → y ≠ (block538S4 : ℝ) → 0 < block538V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block538RightL : ℝ) (block538RightR : ℝ) →
    y ≠ 0 → y ≠ (block538S1 : ℝ) → y ≠ (block538S2 : ℝ) →
    y ≠ (block538S3 : ℝ) → y ≠ (block538S4 : ℝ) → 0 < block538V y)

theorem block538_reallog_certificate_proof :
    block538_reallog_certificate := by
  exact ⟨block538_left_V_pos, block538_right_V_pos⟩

end Block538
end M1817475
end Erdos1038Lean
