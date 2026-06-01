import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block548

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block548

open Set

def block548W1 : Rat := ((3896947667283747 : Rat) / 10000000000000000)
def block548W2 : Rat := (0 : Rat)
def block548W3 : Rat := ((573802399635871 : Rat) / 1250000000000000)
def block548W4 : Rat := (0 : Rat)
def block548S1 : Rat := ((18174751 : Rat) / 10000000)
def block548S2 : Rat := ((511587 : Rat) / 200000)
def block548S3 : Rat := ((129420646517857143047 : Rat) / 50000000000000000000)
def block548S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block548V (y : ℝ) : ℝ :=
  ratPotential block548W1 block548W2 block548W3 block548W4 block548S1 block548S2 block548S3 block548S4 y

def block548LeftParamsCertificate : Bool :=
  allBoxesSameParams block548LeftBoxes block548W1 block548W2 block548W3 block548W4 block548S1 block548S2 block548S3 block548S4

theorem block548LeftParamsCertificate_eq_true :
    block548LeftParamsCertificate = true := by
  native_decide

theorem block548_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block548LeftL : ℝ) (block548LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block548S1 : ℝ))
    (hy2ne : y ≠ (block548S2 : ℝ))
    (hy3ne : y ≠ (block548S3 : ℝ))
    (hy4ne : y ≠ (block548S4 : ℝ)) :
    0 < block548V y := by
  have hcert := block548LeftCertificate_eq_true
  unfold block548LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block548LeftBoxes) (lo := block548LeftL) (hi := block548LeftR)
    (w1 := block548W1) (w2 := block548W2) (w3 := block548W3) (w4 := block548W4)
    (s1 := block548S1) (s2 := block548S2) (s3 := block548S3) (s4 := block548S4)
    hboxes hcover block548LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block548RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block548RightChunk000 block548W1 block548W2 block548W3 block548W4 block548S1 block548S2 block548S3 block548S4

theorem block548RightChunk000ParamsCertificate_eq_true :
    block548RightChunk000ParamsCertificate = true := by
  native_decide

theorem block548_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block548RightChunk000L : ℝ) (block548RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block548S1 : ℝ))
    (hy2ne : y ≠ (block548S2 : ℝ))
    (hy3ne : y ≠ (block548S3 : ℝ))
    (hy4ne : y ≠ (block548S4 : ℝ)) :
    0 < block548V y := by
  have hcert := block548RightChunk000Certificate_eq_true
  unfold block548RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block548RightChunk000) (lo := block548RightChunk000L) (hi := block548RightChunk000R)
    (w1 := block548W1) (w2 := block548W2) (w3 := block548W3) (w4 := block548W4)
    (s1 := block548S1) (s2 := block548S2) (s3 := block548S3) (s4 := block548S4)
    hboxes hcover block548RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block548_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block548RightL : ℝ) (block548RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block548S1 : ℝ))
    (hy2ne : y ≠ (block548S2 : ℝ))
    (hy3ne : y ≠ (block548S3 : ℝ))
    (hy4ne : y ≠ (block548S4 : ℝ)) :
    0 < block548V y := by
  have hL : (block548RightChunk000L : ℝ) = (block548RightL : ℝ) := by
    norm_num [block548RightChunk000L, block548RightL]
  have hR : (block548RightChunk000R : ℝ) = (block548RightR : ℝ) := by
    norm_num [block548RightChunk000R, block548RightR]
  have hyc : y ∈ Icc (block548RightChunk000L : ℝ) (block548RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block548_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block548_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block548LeftL : ℝ) (block548LeftR : ℝ) →
    y ≠ 0 → y ≠ (block548S1 : ℝ) → y ≠ (block548S2 : ℝ) →
    y ≠ (block548S3 : ℝ) → y ≠ (block548S4 : ℝ) → 0 < block548V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block548RightL : ℝ) (block548RightR : ℝ) →
    y ≠ 0 → y ≠ (block548S1 : ℝ) → y ≠ (block548S2 : ℝ) →
    y ≠ (block548S3 : ℝ) → y ≠ (block548S4 : ℝ) → 0 < block548V y)

theorem block548_reallog_certificate_proof :
    block548_reallog_certificate := by
  exact ⟨block548_left_V_pos, block548_right_V_pos⟩

end Block548
end M1817475
end Erdos1038Lean
