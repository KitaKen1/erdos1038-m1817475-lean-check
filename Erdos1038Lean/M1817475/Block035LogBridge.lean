import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block035

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block035

open Set

def block035W1 : Rat := ((2441736440717907 : Rat) / 1000000000000000)
def block035W2 : Rat := (0 : Rat)
def block035W3 : Rat := (0 : Rat)
def block035W4 : Rat := ((874205438317493 : Rat) / 3125000000000000)
def block035S1 : Rat := ((18174751 : Rat) / 10000000)
def block035S2 : Rat := ((511587 : Rat) / 200000)
def block035S3 : Rat := ((107000619 : Rat) / 40000000)
def block035S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block035V (y : ℝ) : ℝ :=
  ratPotential block035W1 block035W2 block035W3 block035W4 block035S1 block035S2 block035S3 block035S4 y

def block035LeftParamsCertificate : Bool :=
  allBoxesSameParams block035LeftBoxes block035W1 block035W2 block035W3 block035W4 block035S1 block035S2 block035S3 block035S4

theorem block035LeftParamsCertificate_eq_true :
    block035LeftParamsCertificate = true := by
  native_decide

theorem block035_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block035LeftL : ℝ) (block035LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block035S1 : ℝ))
    (hy2ne : y ≠ (block035S2 : ℝ))
    (hy3ne : y ≠ (block035S3 : ℝ))
    (hy4ne : y ≠ (block035S4 : ℝ)) :
    0 < block035V y := by
  have hcert := block035LeftCertificate_eq_true
  unfold block035LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block035LeftBoxes) (lo := block035LeftL) (hi := block035LeftR)
    (w1 := block035W1) (w2 := block035W2) (w3 := block035W3) (w4 := block035W4)
    (s1 := block035S1) (s2 := block035S2) (s3 := block035S3) (s4 := block035S4)
    hboxes hcover block035LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block035RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block035RightChunk000 block035W1 block035W2 block035W3 block035W4 block035S1 block035S2 block035S3 block035S4

theorem block035RightChunk000ParamsCertificate_eq_true :
    block035RightChunk000ParamsCertificate = true := by
  native_decide

theorem block035_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block035RightChunk000L : ℝ) (block035RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block035S1 : ℝ))
    (hy2ne : y ≠ (block035S2 : ℝ))
    (hy3ne : y ≠ (block035S3 : ℝ))
    (hy4ne : y ≠ (block035S4 : ℝ)) :
    0 < block035V y := by
  have hcert := block035RightChunk000Certificate_eq_true
  unfold block035RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block035RightChunk000) (lo := block035RightChunk000L) (hi := block035RightChunk000R)
    (w1 := block035W1) (w2 := block035W2) (w3 := block035W3) (w4 := block035W4)
    (s1 := block035S1) (s2 := block035S2) (s3 := block035S3) (s4 := block035S4)
    hboxes hcover block035RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block035_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block035RightL : ℝ) (block035RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block035S1 : ℝ))
    (hy2ne : y ≠ (block035S2 : ℝ))
    (hy3ne : y ≠ (block035S3 : ℝ))
    (hy4ne : y ≠ (block035S4 : ℝ)) :
    0 < block035V y := by
  have hL : (block035RightChunk000L : ℝ) = (block035RightL : ℝ) := by
    norm_num [block035RightChunk000L, block035RightL]
  have hR : (block035RightChunk000R : ℝ) = (block035RightR : ℝ) := by
    norm_num [block035RightChunk000R, block035RightR]
  have hyc : y ∈ Icc (block035RightChunk000L : ℝ) (block035RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block035_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block035_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block035LeftL : ℝ) (block035LeftR : ℝ) →
    y ≠ 0 → y ≠ (block035S1 : ℝ) → y ≠ (block035S2 : ℝ) →
    y ≠ (block035S3 : ℝ) → y ≠ (block035S4 : ℝ) → 0 < block035V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block035RightL : ℝ) (block035RightR : ℝ) →
    y ≠ 0 → y ≠ (block035S1 : ℝ) → y ≠ (block035S2 : ℝ) →
    y ≠ (block035S3 : ℝ) → y ≠ (block035S4 : ℝ) → 0 < block035V y)

theorem block035_reallog_certificate_proof :
    block035_reallog_certificate := by
  exact ⟨block035_left_V_pos, block035_right_V_pos⟩

end Block035
end M1817475
end Erdos1038Lean
