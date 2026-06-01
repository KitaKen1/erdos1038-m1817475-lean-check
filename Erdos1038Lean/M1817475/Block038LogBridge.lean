import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block038

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block038

open Set

def block038W1 : Rat := ((24855791077763483 : Rat) / 10000000000000000)
def block038W2 : Rat := (0 : Rat)
def block038W3 : Rat := (0 : Rat)
def block038W4 : Rat := ((13878725512969123 : Rat) / 50000000000000000)
def block038S1 : Rat := ((18174751 : Rat) / 10000000)
def block038S2 : Rat := ((511587 : Rat) / 200000)
def block038S3 : Rat := ((107000619 : Rat) / 40000000)
def block038S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block038V (y : ℝ) : ℝ :=
  ratPotential block038W1 block038W2 block038W3 block038W4 block038S1 block038S2 block038S3 block038S4 y

def block038LeftParamsCertificate : Bool :=
  allBoxesSameParams block038LeftBoxes block038W1 block038W2 block038W3 block038W4 block038S1 block038S2 block038S3 block038S4

theorem block038LeftParamsCertificate_eq_true :
    block038LeftParamsCertificate = true := by
  native_decide

theorem block038_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block038LeftL : ℝ) (block038LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block038S1 : ℝ))
    (hy2ne : y ≠ (block038S2 : ℝ))
    (hy3ne : y ≠ (block038S3 : ℝ))
    (hy4ne : y ≠ (block038S4 : ℝ)) :
    0 < block038V y := by
  have hcert := block038LeftCertificate_eq_true
  unfold block038LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block038LeftBoxes) (lo := block038LeftL) (hi := block038LeftR)
    (w1 := block038W1) (w2 := block038W2) (w3 := block038W3) (w4 := block038W4)
    (s1 := block038S1) (s2 := block038S2) (s3 := block038S3) (s4 := block038S4)
    hboxes hcover block038LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block038RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block038RightChunk000 block038W1 block038W2 block038W3 block038W4 block038S1 block038S2 block038S3 block038S4

theorem block038RightChunk000ParamsCertificate_eq_true :
    block038RightChunk000ParamsCertificate = true := by
  native_decide

theorem block038_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block038RightChunk000L : ℝ) (block038RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block038S1 : ℝ))
    (hy2ne : y ≠ (block038S2 : ℝ))
    (hy3ne : y ≠ (block038S3 : ℝ))
    (hy4ne : y ≠ (block038S4 : ℝ)) :
    0 < block038V y := by
  have hcert := block038RightChunk000Certificate_eq_true
  unfold block038RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block038RightChunk000) (lo := block038RightChunk000L) (hi := block038RightChunk000R)
    (w1 := block038W1) (w2 := block038W2) (w3 := block038W3) (w4 := block038W4)
    (s1 := block038S1) (s2 := block038S2) (s3 := block038S3) (s4 := block038S4)
    hboxes hcover block038RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block038_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block038RightL : ℝ) (block038RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block038S1 : ℝ))
    (hy2ne : y ≠ (block038S2 : ℝ))
    (hy3ne : y ≠ (block038S3 : ℝ))
    (hy4ne : y ≠ (block038S4 : ℝ)) :
    0 < block038V y := by
  have hL : (block038RightChunk000L : ℝ) = (block038RightL : ℝ) := by
    norm_num [block038RightChunk000L, block038RightL]
  have hR : (block038RightChunk000R : ℝ) = (block038RightR : ℝ) := by
    norm_num [block038RightChunk000R, block038RightR]
  have hyc : y ∈ Icc (block038RightChunk000L : ℝ) (block038RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block038_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block038_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block038LeftL : ℝ) (block038LeftR : ℝ) →
    y ≠ 0 → y ≠ (block038S1 : ℝ) → y ≠ (block038S2 : ℝ) →
    y ≠ (block038S3 : ℝ) → y ≠ (block038S4 : ℝ) → 0 < block038V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block038RightL : ℝ) (block038RightR : ℝ) →
    y ≠ 0 → y ≠ (block038S1 : ℝ) → y ≠ (block038S2 : ℝ) →
    y ≠ (block038S3 : ℝ) → y ≠ (block038S4 : ℝ) → 0 < block038V y)

theorem block038_reallog_certificate_proof :
    block038_reallog_certificate := by
  exact ⟨block038_left_V_pos, block038_right_V_pos⟩

end Block038
end M1817475
end Erdos1038Lean
