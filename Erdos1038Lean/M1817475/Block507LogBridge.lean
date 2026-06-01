import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block507

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block507

open Set

def block507W1 : Rat := ((8866596471327901 : Rat) / 20000000000000000)
def block507W2 : Rat := (0 : Rat)
def block507W3 : Rat := ((4298965328442127 : Rat) / 10000000000000000)
def block507W4 : Rat := ((2092928778225803 : Rat) / 200000000000000000)
def block507S1 : Rat := ((18174751 : Rat) / 10000000)
def block507S2 : Rat := ((511587 : Rat) / 200000)
def block507S3 : Rat := ((130222159910714285869 : Rat) / 50000000000000000000)
def block507S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block507V (y : ℝ) : ℝ :=
  ratPotential block507W1 block507W2 block507W3 block507W4 block507S1 block507S2 block507S3 block507S4 y

def block507LeftParamsCertificate : Bool :=
  allBoxesSameParams block507LeftBoxes block507W1 block507W2 block507W3 block507W4 block507S1 block507S2 block507S3 block507S4

theorem block507LeftParamsCertificate_eq_true :
    block507LeftParamsCertificate = true := by
  native_decide

theorem block507_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block507LeftL : ℝ) (block507LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block507S1 : ℝ))
    (hy2ne : y ≠ (block507S2 : ℝ))
    (hy3ne : y ≠ (block507S3 : ℝ))
    (hy4ne : y ≠ (block507S4 : ℝ)) :
    0 < block507V y := by
  have hcert := block507LeftCertificate_eq_true
  unfold block507LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block507LeftBoxes) (lo := block507LeftL) (hi := block507LeftR)
    (w1 := block507W1) (w2 := block507W2) (w3 := block507W3) (w4 := block507W4)
    (s1 := block507S1) (s2 := block507S2) (s3 := block507S3) (s4 := block507S4)
    hboxes hcover block507LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block507RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block507RightChunk000 block507W1 block507W2 block507W3 block507W4 block507S1 block507S2 block507S3 block507S4

theorem block507RightChunk000ParamsCertificate_eq_true :
    block507RightChunk000ParamsCertificate = true := by
  native_decide

theorem block507_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block507RightChunk000L : ℝ) (block507RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block507S1 : ℝ))
    (hy2ne : y ≠ (block507S2 : ℝ))
    (hy3ne : y ≠ (block507S3 : ℝ))
    (hy4ne : y ≠ (block507S4 : ℝ)) :
    0 < block507V y := by
  have hcert := block507RightChunk000Certificate_eq_true
  unfold block507RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block507RightChunk000) (lo := block507RightChunk000L) (hi := block507RightChunk000R)
    (w1 := block507W1) (w2 := block507W2) (w3 := block507W3) (w4 := block507W4)
    (s1 := block507S1) (s2 := block507S2) (s3 := block507S3) (s4 := block507S4)
    hboxes hcover block507RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block507_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block507RightL : ℝ) (block507RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block507S1 : ℝ))
    (hy2ne : y ≠ (block507S2 : ℝ))
    (hy3ne : y ≠ (block507S3 : ℝ))
    (hy4ne : y ≠ (block507S4 : ℝ)) :
    0 < block507V y := by
  have hL : (block507RightChunk000L : ℝ) = (block507RightL : ℝ) := by
    norm_num [block507RightChunk000L, block507RightL]
  have hR : (block507RightChunk000R : ℝ) = (block507RightR : ℝ) := by
    norm_num [block507RightChunk000R, block507RightR]
  have hyc : y ∈ Icc (block507RightChunk000L : ℝ) (block507RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block507_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block507_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block507LeftL : ℝ) (block507LeftR : ℝ) →
    y ≠ 0 → y ≠ (block507S1 : ℝ) → y ≠ (block507S2 : ℝ) →
    y ≠ (block507S3 : ℝ) → y ≠ (block507S4 : ℝ) → 0 < block507V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block507RightL : ℝ) (block507RightR : ℝ) →
    y ≠ 0 → y ≠ (block507S1 : ℝ) → y ≠ (block507S2 : ℝ) →
    y ≠ (block507S3 : ℝ) → y ≠ (block507S4 : ℝ) → 0 < block507V y)

theorem block507_reallog_certificate_proof :
    block507_reallog_certificate := by
  exact ⟨block507_left_V_pos, block507_right_V_pos⟩

end Block507
end M1817475
end Erdos1038Lean
