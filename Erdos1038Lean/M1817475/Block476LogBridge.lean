import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block476

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block476

open Set

def block476W1 : Rat := ((5252997143616281 : Rat) / 10000000000000000)
def block476W2 : Rat := (0 : Rat)
def block476W3 : Rat := ((1857499597112413 : Rat) / 5000000000000000)
def block476W4 : Rat := ((918665152607477 : Rat) / 20000000000000000)
def block476S1 : Rat := ((18174751 : Rat) / 10000000)
def block476S2 : Rat := ((511587 : Rat) / 200000)
def block476S3 : Rat := ((130828182232142857271 : Rat) / 50000000000000000000)
def block476S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block476V (y : ℝ) : ℝ :=
  ratPotential block476W1 block476W2 block476W3 block476W4 block476S1 block476S2 block476S3 block476S4 y

def block476LeftParamsCertificate : Bool :=
  allBoxesSameParams block476LeftBoxes block476W1 block476W2 block476W3 block476W4 block476S1 block476S2 block476S3 block476S4

theorem block476LeftParamsCertificate_eq_true :
    block476LeftParamsCertificate = true := by
  native_decide

theorem block476_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block476LeftL : ℝ) (block476LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block476S1 : ℝ))
    (hy2ne : y ≠ (block476S2 : ℝ))
    (hy3ne : y ≠ (block476S3 : ℝ))
    (hy4ne : y ≠ (block476S4 : ℝ)) :
    0 < block476V y := by
  have hcert := block476LeftCertificate_eq_true
  unfold block476LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block476LeftBoxes) (lo := block476LeftL) (hi := block476LeftR)
    (w1 := block476W1) (w2 := block476W2) (w3 := block476W3) (w4 := block476W4)
    (s1 := block476S1) (s2 := block476S2) (s3 := block476S3) (s4 := block476S4)
    hboxes hcover block476LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block476RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block476RightChunk000 block476W1 block476W2 block476W3 block476W4 block476S1 block476S2 block476S3 block476S4

theorem block476RightChunk000ParamsCertificate_eq_true :
    block476RightChunk000ParamsCertificate = true := by
  native_decide

theorem block476_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block476RightChunk000L : ℝ) (block476RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block476S1 : ℝ))
    (hy2ne : y ≠ (block476S2 : ℝ))
    (hy3ne : y ≠ (block476S3 : ℝ))
    (hy4ne : y ≠ (block476S4 : ℝ)) :
    0 < block476V y := by
  have hcert := block476RightChunk000Certificate_eq_true
  unfold block476RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block476RightChunk000) (lo := block476RightChunk000L) (hi := block476RightChunk000R)
    (w1 := block476W1) (w2 := block476W2) (w3 := block476W3) (w4 := block476W4)
    (s1 := block476S1) (s2 := block476S2) (s3 := block476S3) (s4 := block476S4)
    hboxes hcover block476RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block476_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block476RightL : ℝ) (block476RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block476S1 : ℝ))
    (hy2ne : y ≠ (block476S2 : ℝ))
    (hy3ne : y ≠ (block476S3 : ℝ))
    (hy4ne : y ≠ (block476S4 : ℝ)) :
    0 < block476V y := by
  have hL : (block476RightChunk000L : ℝ) = (block476RightL : ℝ) := by
    norm_num [block476RightChunk000L, block476RightL]
  have hR : (block476RightChunk000R : ℝ) = (block476RightR : ℝ) := by
    norm_num [block476RightChunk000R, block476RightR]
  have hyc : y ∈ Icc (block476RightChunk000L : ℝ) (block476RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block476_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block476_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block476LeftL : ℝ) (block476LeftR : ℝ) →
    y ≠ 0 → y ≠ (block476S1 : ℝ) → y ≠ (block476S2 : ℝ) →
    y ≠ (block476S3 : ℝ) → y ≠ (block476S4 : ℝ) → 0 < block476V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block476RightL : ℝ) (block476RightR : ℝ) →
    y ≠ 0 → y ≠ (block476S1 : ℝ) → y ≠ (block476S2 : ℝ) →
    y ≠ (block476S3 : ℝ) → y ≠ (block476S4 : ℝ) → 0 < block476V y)

theorem block476_reallog_certificate_proof :
    block476_reallog_certificate := by
  exact ⟨block476_left_V_pos, block476_right_V_pos⟩

end Block476
end M1817475
end Erdos1038Lean
