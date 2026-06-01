import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block066

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block066

open Set

def block066W1 : Rat := ((5975902744234447 : Rat) / 2000000000000000)
def block066W2 : Rat := (0 : Rat)
def block066W3 : Rat := (0 : Rat)
def block066W4 : Rat := ((2551146925533777 : Rat) / 10000000000000000)
def block066S1 : Rat := ((18174751 : Rat) / 10000000)
def block066S2 : Rat := ((511587 : Rat) / 200000)
def block066S3 : Rat := ((107000619 : Rat) / 40000000)
def block066S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block066V (y : ℝ) : ℝ :=
  ratPotential block066W1 block066W2 block066W3 block066W4 block066S1 block066S2 block066S3 block066S4 y

def block066LeftParamsCertificate : Bool :=
  allBoxesSameParams block066LeftBoxes block066W1 block066W2 block066W3 block066W4 block066S1 block066S2 block066S3 block066S4

theorem block066LeftParamsCertificate_eq_true :
    block066LeftParamsCertificate = true := by
  native_decide

theorem block066_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block066LeftL : ℝ) (block066LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block066S1 : ℝ))
    (hy2ne : y ≠ (block066S2 : ℝ))
    (hy3ne : y ≠ (block066S3 : ℝ))
    (hy4ne : y ≠ (block066S4 : ℝ)) :
    0 < block066V y := by
  have hcert := block066LeftCertificate_eq_true
  unfold block066LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block066LeftBoxes) (lo := block066LeftL) (hi := block066LeftR)
    (w1 := block066W1) (w2 := block066W2) (w3 := block066W3) (w4 := block066W4)
    (s1 := block066S1) (s2 := block066S2) (s3 := block066S3) (s4 := block066S4)
    hboxes hcover block066LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block066RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block066RightChunk000 block066W1 block066W2 block066W3 block066W4 block066S1 block066S2 block066S3 block066S4

theorem block066RightChunk000ParamsCertificate_eq_true :
    block066RightChunk000ParamsCertificate = true := by
  native_decide

theorem block066_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block066RightChunk000L : ℝ) (block066RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block066S1 : ℝ))
    (hy2ne : y ≠ (block066S2 : ℝ))
    (hy3ne : y ≠ (block066S3 : ℝ))
    (hy4ne : y ≠ (block066S4 : ℝ)) :
    0 < block066V y := by
  have hcert := block066RightChunk000Certificate_eq_true
  unfold block066RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block066RightChunk000) (lo := block066RightChunk000L) (hi := block066RightChunk000R)
    (w1 := block066W1) (w2 := block066W2) (w3 := block066W3) (w4 := block066W4)
    (s1 := block066S1) (s2 := block066S2) (s3 := block066S3) (s4 := block066S4)
    hboxes hcover block066RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block066_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block066RightL : ℝ) (block066RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block066S1 : ℝ))
    (hy2ne : y ≠ (block066S2 : ℝ))
    (hy3ne : y ≠ (block066S3 : ℝ))
    (hy4ne : y ≠ (block066S4 : ℝ)) :
    0 < block066V y := by
  have hL : (block066RightChunk000L : ℝ) = (block066RightL : ℝ) := by
    norm_num [block066RightChunk000L, block066RightL]
  have hR : (block066RightChunk000R : ℝ) = (block066RightR : ℝ) := by
    norm_num [block066RightChunk000R, block066RightR]
  have hyc : y ∈ Icc (block066RightChunk000L : ℝ) (block066RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block066_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block066_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block066LeftL : ℝ) (block066LeftR : ℝ) →
    y ≠ 0 → y ≠ (block066S1 : ℝ) → y ≠ (block066S2 : ℝ) →
    y ≠ (block066S3 : ℝ) → y ≠ (block066S4 : ℝ) → 0 < block066V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block066RightL : ℝ) (block066RightR : ℝ) →
    y ≠ 0 → y ≠ (block066S1 : ℝ) → y ≠ (block066S2 : ℝ) →
    y ≠ (block066S3 : ℝ) → y ≠ (block066S4 : ℝ) → 0 < block066V y)

theorem block066_reallog_certificate_proof :
    block066_reallog_certificate := by
  exact ⟨block066_left_V_pos, block066_right_V_pos⟩

end Block066
end M1817475
end Erdos1038Lean
