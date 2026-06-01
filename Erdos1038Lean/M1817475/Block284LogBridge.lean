import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block284

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block284

open Set

def block284W1 : Rat := ((1029005226305071 : Rat) / 1000000000000000)
def block284W2 : Rat := ((3502422578051607 : Rat) / 100000000000000000)
def block284W3 : Rat := ((5675480088134447 : Rat) / 20000000000000000)
def block284W4 : Rat := (0 : Rat)
def block284S1 : Rat := ((18174751 : Rat) / 10000000)
def block284S2 : Rat := ((511587 : Rat) / 200000)
def block284S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block284S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block284V (y : ℝ) : ℝ :=
  ratPotential block284W1 block284W2 block284W3 block284W4 block284S1 block284S2 block284S3 block284S4 y

def block284LeftParamsCertificate : Bool :=
  allBoxesSameParams block284LeftBoxes block284W1 block284W2 block284W3 block284W4 block284S1 block284S2 block284S3 block284S4

theorem block284LeftParamsCertificate_eq_true :
    block284LeftParamsCertificate = true := by
  native_decide

theorem block284_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block284LeftL : ℝ) (block284LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block284S1 : ℝ))
    (hy2ne : y ≠ (block284S2 : ℝ))
    (hy3ne : y ≠ (block284S3 : ℝ))
    (hy4ne : y ≠ (block284S4 : ℝ)) :
    0 < block284V y := by
  have hcert := block284LeftCertificate_eq_true
  unfold block284LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block284LeftBoxes) (lo := block284LeftL) (hi := block284LeftR)
    (w1 := block284W1) (w2 := block284W2) (w3 := block284W3) (w4 := block284W4)
    (s1 := block284S1) (s2 := block284S2) (s3 := block284S3) (s4 := block284S4)
    hboxes hcover block284LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block284RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block284RightChunk000 block284W1 block284W2 block284W3 block284W4 block284S1 block284S2 block284S3 block284S4

theorem block284RightChunk000ParamsCertificate_eq_true :
    block284RightChunk000ParamsCertificate = true := by
  native_decide

theorem block284_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block284RightChunk000L : ℝ) (block284RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block284S1 : ℝ))
    (hy2ne : y ≠ (block284S2 : ℝ))
    (hy3ne : y ≠ (block284S3 : ℝ))
    (hy4ne : y ≠ (block284S4 : ℝ)) :
    0 < block284V y := by
  have hcert := block284RightChunk000Certificate_eq_true
  unfold block284RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block284RightChunk000) (lo := block284RightChunk000L) (hi := block284RightChunk000R)
    (w1 := block284W1) (w2 := block284W2) (w3 := block284W3) (w4 := block284W4)
    (s1 := block284S1) (s2 := block284S2) (s3 := block284S3) (s4 := block284S4)
    hboxes hcover block284RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block284_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block284RightL : ℝ) (block284RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block284S1 : ℝ))
    (hy2ne : y ≠ (block284S2 : ℝ))
    (hy3ne : y ≠ (block284S3 : ℝ))
    (hy4ne : y ≠ (block284S4 : ℝ)) :
    0 < block284V y := by
  have hL : (block284RightChunk000L : ℝ) = (block284RightL : ℝ) := by
    norm_num [block284RightChunk000L, block284RightL]
  have hR : (block284RightChunk000R : ℝ) = (block284RightR : ℝ) := by
    norm_num [block284RightChunk000R, block284RightR]
  have hyc : y ∈ Icc (block284RightChunk000L : ℝ) (block284RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block284_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block284_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block284LeftL : ℝ) (block284LeftR : ℝ) →
    y ≠ 0 → y ≠ (block284S1 : ℝ) → y ≠ (block284S2 : ℝ) →
    y ≠ (block284S3 : ℝ) → y ≠ (block284S4 : ℝ) → 0 < block284V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block284RightL : ℝ) (block284RightR : ℝ) →
    y ≠ 0 → y ≠ (block284S1 : ℝ) → y ≠ (block284S2 : ℝ) →
    y ≠ (block284S3 : ℝ) → y ≠ (block284S4 : ℝ) → 0 < block284V y)

theorem block284_reallog_certificate_proof :
    block284_reallog_certificate := by
  exact ⟨block284_left_V_pos, block284_right_V_pos⟩

end Block284
end M1817475
end Erdos1038Lean
