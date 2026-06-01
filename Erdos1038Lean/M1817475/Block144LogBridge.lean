import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block144

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block144

open Set

def block144W1 : Rat := ((24016667123980513 : Rat) / 10000000000000000)
def block144W2 : Rat := (0 : Rat)
def block144W3 : Rat := ((172100548881553 : Rat) / 1250000000000000)
def block144W4 : Rat := ((5264391501374053 : Rat) / 50000000000000000)
def block144S1 : Rat := ((18174751 : Rat) / 10000000)
def block144S2 : Rat := ((511587 : Rat) / 200000)
def block144S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block144S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block144V (y : ℝ) : ℝ :=
  ratPotential block144W1 block144W2 block144W3 block144W4 block144S1 block144S2 block144S3 block144S4 y

def block144LeftParamsCertificate : Bool :=
  allBoxesSameParams block144LeftBoxes block144W1 block144W2 block144W3 block144W4 block144S1 block144S2 block144S3 block144S4

theorem block144LeftParamsCertificate_eq_true :
    block144LeftParamsCertificate = true := by
  native_decide

theorem block144_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block144LeftL : ℝ) (block144LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block144S1 : ℝ))
    (hy2ne : y ≠ (block144S2 : ℝ))
    (hy3ne : y ≠ (block144S3 : ℝ))
    (hy4ne : y ≠ (block144S4 : ℝ)) :
    0 < block144V y := by
  have hcert := block144LeftCertificate_eq_true
  unfold block144LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block144LeftBoxes) (lo := block144LeftL) (hi := block144LeftR)
    (w1 := block144W1) (w2 := block144W2) (w3 := block144W3) (w4 := block144W4)
    (s1 := block144S1) (s2 := block144S2) (s3 := block144S3) (s4 := block144S4)
    hboxes hcover block144LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block144RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block144RightChunk000 block144W1 block144W2 block144W3 block144W4 block144S1 block144S2 block144S3 block144S4

theorem block144RightChunk000ParamsCertificate_eq_true :
    block144RightChunk000ParamsCertificate = true := by
  native_decide

theorem block144_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block144RightChunk000L : ℝ) (block144RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block144S1 : ℝ))
    (hy2ne : y ≠ (block144S2 : ℝ))
    (hy3ne : y ≠ (block144S3 : ℝ))
    (hy4ne : y ≠ (block144S4 : ℝ)) :
    0 < block144V y := by
  have hcert := block144RightChunk000Certificate_eq_true
  unfold block144RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block144RightChunk000) (lo := block144RightChunk000L) (hi := block144RightChunk000R)
    (w1 := block144W1) (w2 := block144W2) (w3 := block144W3) (w4 := block144W4)
    (s1 := block144S1) (s2 := block144S2) (s3 := block144S3) (s4 := block144S4)
    hboxes hcover block144RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block144_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block144RightL : ℝ) (block144RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block144S1 : ℝ))
    (hy2ne : y ≠ (block144S2 : ℝ))
    (hy3ne : y ≠ (block144S3 : ℝ))
    (hy4ne : y ≠ (block144S4 : ℝ)) :
    0 < block144V y := by
  have hL : (block144RightChunk000L : ℝ) = (block144RightL : ℝ) := by
    norm_num [block144RightChunk000L, block144RightL]
  have hR : (block144RightChunk000R : ℝ) = (block144RightR : ℝ) := by
    norm_num [block144RightChunk000R, block144RightR]
  have hyc : y ∈ Icc (block144RightChunk000L : ℝ) (block144RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block144_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block144_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block144LeftL : ℝ) (block144LeftR : ℝ) →
    y ≠ 0 → y ≠ (block144S1 : ℝ) → y ≠ (block144S2 : ℝ) →
    y ≠ (block144S3 : ℝ) → y ≠ (block144S4 : ℝ) → 0 < block144V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block144RightL : ℝ) (block144RightR : ℝ) →
    y ≠ 0 → y ≠ (block144S1 : ℝ) → y ≠ (block144S2 : ℝ) →
    y ≠ (block144S3 : ℝ) → y ≠ (block144S4 : ℝ) → 0 < block144V y)

theorem block144_reallog_certificate_proof :
    block144_reallog_certificate := by
  exact ⟨block144_left_V_pos, block144_right_V_pos⟩

end Block144
end M1817475
end Erdos1038Lean
