import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block534

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block534

open Set

def block534W1 : Rat := ((10092746342211599 : Rat) / 25000000000000000)
def block534W2 : Rat := (0 : Rat)
def block534W3 : Rat := ((2268557036922511 : Rat) / 5000000000000000)
def block534W4 : Rat := (0 : Rat)
def block534S1 : Rat := ((18174751 : Rat) / 10000000)
def block534S2 : Rat := ((511587 : Rat) / 200000)
def block534S3 : Rat := ((25938866803571428607 : Rat) / 10000000000000000000)
def block534S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block534V (y : ℝ) : ℝ :=
  ratPotential block534W1 block534W2 block534W3 block534W4 block534S1 block534S2 block534S3 block534S4 y

def block534LeftParamsCertificate : Bool :=
  allBoxesSameParams block534LeftBoxes block534W1 block534W2 block534W3 block534W4 block534S1 block534S2 block534S3 block534S4

theorem block534LeftParamsCertificate_eq_true :
    block534LeftParamsCertificate = true := by
  native_decide

theorem block534_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block534LeftL : ℝ) (block534LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block534S1 : ℝ))
    (hy2ne : y ≠ (block534S2 : ℝ))
    (hy3ne : y ≠ (block534S3 : ℝ))
    (hy4ne : y ≠ (block534S4 : ℝ)) :
    0 < block534V y := by
  have hcert := block534LeftCertificate_eq_true
  unfold block534LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block534LeftBoxes) (lo := block534LeftL) (hi := block534LeftR)
    (w1 := block534W1) (w2 := block534W2) (w3 := block534W3) (w4 := block534W4)
    (s1 := block534S1) (s2 := block534S2) (s3 := block534S3) (s4 := block534S4)
    hboxes hcover block534LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block534RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block534RightChunk000 block534W1 block534W2 block534W3 block534W4 block534S1 block534S2 block534S3 block534S4

theorem block534RightChunk000ParamsCertificate_eq_true :
    block534RightChunk000ParamsCertificate = true := by
  native_decide

theorem block534_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block534RightChunk000L : ℝ) (block534RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block534S1 : ℝ))
    (hy2ne : y ≠ (block534S2 : ℝ))
    (hy3ne : y ≠ (block534S3 : ℝ))
    (hy4ne : y ≠ (block534S4 : ℝ)) :
    0 < block534V y := by
  have hcert := block534RightChunk000Certificate_eq_true
  unfold block534RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block534RightChunk000) (lo := block534RightChunk000L) (hi := block534RightChunk000R)
    (w1 := block534W1) (w2 := block534W2) (w3 := block534W3) (w4 := block534W4)
    (s1 := block534S1) (s2 := block534S2) (s3 := block534S3) (s4 := block534S4)
    hboxes hcover block534RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block534_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block534RightL : ℝ) (block534RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block534S1 : ℝ))
    (hy2ne : y ≠ (block534S2 : ℝ))
    (hy3ne : y ≠ (block534S3 : ℝ))
    (hy4ne : y ≠ (block534S4 : ℝ)) :
    0 < block534V y := by
  have hL : (block534RightChunk000L : ℝ) = (block534RightL : ℝ) := by
    norm_num [block534RightChunk000L, block534RightL]
  have hR : (block534RightChunk000R : ℝ) = (block534RightR : ℝ) := by
    norm_num [block534RightChunk000R, block534RightR]
  have hyc : y ∈ Icc (block534RightChunk000L : ℝ) (block534RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block534_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block534_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block534LeftL : ℝ) (block534LeftR : ℝ) →
    y ≠ 0 → y ≠ (block534S1 : ℝ) → y ≠ (block534S2 : ℝ) →
    y ≠ (block534S3 : ℝ) → y ≠ (block534S4 : ℝ) → 0 < block534V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block534RightL : ℝ) (block534RightR : ℝ) →
    y ≠ 0 → y ≠ (block534S1 : ℝ) → y ≠ (block534S2 : ℝ) →
    y ≠ (block534S3 : ℝ) → y ≠ (block534S4 : ℝ) → 0 < block534V y)

theorem block534_reallog_certificate_proof :
    block534_reallog_certificate := by
  exact ⟨block534_left_V_pos, block534_right_V_pos⟩

end Block534
end M1817475
end Erdos1038Lean
