import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block119

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block119

open Set

def block119W1 : Rat := ((11733364721328101 : Rat) / 5000000000000000)
def block119W2 : Rat := (0 : Rat)
def block119W3 : Rat := ((8923726788765413 : Rat) / 100000000000000000)
def block119W4 : Rat := ((3219817059456499 : Rat) / 20000000000000000)
def block119S1 : Rat := ((18174751 : Rat) / 10000000)
def block119S2 : Rat := ((511587 : Rat) / 200000)
def block119S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block119S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block119V (y : ℝ) : ℝ :=
  ratPotential block119W1 block119W2 block119W3 block119W4 block119S1 block119S2 block119S3 block119S4 y

def block119LeftParamsCertificate : Bool :=
  allBoxesSameParams block119LeftBoxes block119W1 block119W2 block119W3 block119W4 block119S1 block119S2 block119S3 block119S4

theorem block119LeftParamsCertificate_eq_true :
    block119LeftParamsCertificate = true := by
  native_decide

theorem block119_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block119LeftL : ℝ) (block119LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block119S1 : ℝ))
    (hy2ne : y ≠ (block119S2 : ℝ))
    (hy3ne : y ≠ (block119S3 : ℝ))
    (hy4ne : y ≠ (block119S4 : ℝ)) :
    0 < block119V y := by
  have hcert := block119LeftCertificate_eq_true
  unfold block119LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block119LeftBoxes) (lo := block119LeftL) (hi := block119LeftR)
    (w1 := block119W1) (w2 := block119W2) (w3 := block119W3) (w4 := block119W4)
    (s1 := block119S1) (s2 := block119S2) (s3 := block119S3) (s4 := block119S4)
    hboxes hcover block119LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block119RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block119RightChunk000 block119W1 block119W2 block119W3 block119W4 block119S1 block119S2 block119S3 block119S4

theorem block119RightChunk000ParamsCertificate_eq_true :
    block119RightChunk000ParamsCertificate = true := by
  native_decide

theorem block119_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block119RightChunk000L : ℝ) (block119RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block119S1 : ℝ))
    (hy2ne : y ≠ (block119S2 : ℝ))
    (hy3ne : y ≠ (block119S3 : ℝ))
    (hy4ne : y ≠ (block119S4 : ℝ)) :
    0 < block119V y := by
  have hcert := block119RightChunk000Certificate_eq_true
  unfold block119RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block119RightChunk000) (lo := block119RightChunk000L) (hi := block119RightChunk000R)
    (w1 := block119W1) (w2 := block119W2) (w3 := block119W3) (w4 := block119W4)
    (s1 := block119S1) (s2 := block119S2) (s3 := block119S3) (s4 := block119S4)
    hboxes hcover block119RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block119_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block119RightL : ℝ) (block119RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block119S1 : ℝ))
    (hy2ne : y ≠ (block119S2 : ℝ))
    (hy3ne : y ≠ (block119S3 : ℝ))
    (hy4ne : y ≠ (block119S4 : ℝ)) :
    0 < block119V y := by
  have hL : (block119RightChunk000L : ℝ) = (block119RightL : ℝ) := by
    norm_num [block119RightChunk000L, block119RightL]
  have hR : (block119RightChunk000R : ℝ) = (block119RightR : ℝ) := by
    norm_num [block119RightChunk000R, block119RightR]
  have hyc : y ∈ Icc (block119RightChunk000L : ℝ) (block119RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block119_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block119_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block119LeftL : ℝ) (block119LeftR : ℝ) →
    y ≠ 0 → y ≠ (block119S1 : ℝ) → y ≠ (block119S2 : ℝ) →
    y ≠ (block119S3 : ℝ) → y ≠ (block119S4 : ℝ) → 0 < block119V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block119RightL : ℝ) (block119RightR : ℝ) →
    y ≠ 0 → y ≠ (block119S1 : ℝ) → y ≠ (block119S2 : ℝ) →
    y ≠ (block119S3 : ℝ) → y ≠ (block119S4 : ℝ) → 0 < block119V y)

theorem block119_reallog_certificate_proof :
    block119_reallog_certificate := by
  exact ⟨block119_left_V_pos, block119_right_V_pos⟩

end Block119
end M1817475
end Erdos1038Lean
