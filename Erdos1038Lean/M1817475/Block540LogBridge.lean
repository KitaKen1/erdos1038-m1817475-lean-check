import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block540

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block540

open Set

def block540W1 : Rat := ((1590526383657747 : Rat) / 4000000000000000)
def block540W2 : Rat := (0 : Rat)
def block540W3 : Rat := ((45599294272510343 : Rat) / 100000000000000000)
def block540W4 : Rat := (0 : Rat)
def block540S1 : Rat := ((18174751 : Rat) / 10000000)
def block540S2 : Rat := ((511587 : Rat) / 200000)
def block540S3 : Rat := ((129577039375000000183 : Rat) / 50000000000000000000)
def block540S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block540V (y : ℝ) : ℝ :=
  ratPotential block540W1 block540W2 block540W3 block540W4 block540S1 block540S2 block540S3 block540S4 y

def block540LeftParamsCertificate : Bool :=
  allBoxesSameParams block540LeftBoxes block540W1 block540W2 block540W3 block540W4 block540S1 block540S2 block540S3 block540S4

theorem block540LeftParamsCertificate_eq_true :
    block540LeftParamsCertificate = true := by
  native_decide

theorem block540_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block540LeftL : ℝ) (block540LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block540S1 : ℝ))
    (hy2ne : y ≠ (block540S2 : ℝ))
    (hy3ne : y ≠ (block540S3 : ℝ))
    (hy4ne : y ≠ (block540S4 : ℝ)) :
    0 < block540V y := by
  have hcert := block540LeftCertificate_eq_true
  unfold block540LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block540LeftBoxes) (lo := block540LeftL) (hi := block540LeftR)
    (w1 := block540W1) (w2 := block540W2) (w3 := block540W3) (w4 := block540W4)
    (s1 := block540S1) (s2 := block540S2) (s3 := block540S3) (s4 := block540S4)
    hboxes hcover block540LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block540RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block540RightChunk000 block540W1 block540W2 block540W3 block540W4 block540S1 block540S2 block540S3 block540S4

theorem block540RightChunk000ParamsCertificate_eq_true :
    block540RightChunk000ParamsCertificate = true := by
  native_decide

theorem block540_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block540RightChunk000L : ℝ) (block540RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block540S1 : ℝ))
    (hy2ne : y ≠ (block540S2 : ℝ))
    (hy3ne : y ≠ (block540S3 : ℝ))
    (hy4ne : y ≠ (block540S4 : ℝ)) :
    0 < block540V y := by
  have hcert := block540RightChunk000Certificate_eq_true
  unfold block540RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block540RightChunk000) (lo := block540RightChunk000L) (hi := block540RightChunk000R)
    (w1 := block540W1) (w2 := block540W2) (w3 := block540W3) (w4 := block540W4)
    (s1 := block540S1) (s2 := block540S2) (s3 := block540S3) (s4 := block540S4)
    hboxes hcover block540RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block540_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block540RightL : ℝ) (block540RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block540S1 : ℝ))
    (hy2ne : y ≠ (block540S2 : ℝ))
    (hy3ne : y ≠ (block540S3 : ℝ))
    (hy4ne : y ≠ (block540S4 : ℝ)) :
    0 < block540V y := by
  have hL : (block540RightChunk000L : ℝ) = (block540RightL : ℝ) := by
    norm_num [block540RightChunk000L, block540RightL]
  have hR : (block540RightChunk000R : ℝ) = (block540RightR : ℝ) := by
    norm_num [block540RightChunk000R, block540RightR]
  have hyc : y ∈ Icc (block540RightChunk000L : ℝ) (block540RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block540_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block540_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block540LeftL : ℝ) (block540LeftR : ℝ) →
    y ≠ 0 → y ≠ (block540S1 : ℝ) → y ≠ (block540S2 : ℝ) →
    y ≠ (block540S3 : ℝ) → y ≠ (block540S4 : ℝ) → 0 < block540V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block540RightL : ℝ) (block540RightR : ℝ) →
    y ≠ 0 → y ≠ (block540S1 : ℝ) → y ≠ (block540S2 : ℝ) →
    y ≠ (block540S3 : ℝ) → y ≠ (block540S4 : ℝ) → 0 < block540V y)

theorem block540_reallog_certificate_proof :
    block540_reallog_certificate := by
  exact ⟨block540_left_V_pos, block540_right_V_pos⟩

end Block540
end M1817475
end Erdos1038Lean
