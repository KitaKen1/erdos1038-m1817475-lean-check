import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block071

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block071

open Set

def block071W1 : Rat := ((3100580376060617 : Rat) / 1000000000000000)
def block071W2 : Rat := (0 : Rat)
def block071W3 : Rat := (0 : Rat)
def block071W4 : Rat := ((5011898689713793 : Rat) / 20000000000000000)
def block071S1 : Rat := ((18174751 : Rat) / 10000000)
def block071S2 : Rat := ((511587 : Rat) / 200000)
def block071S3 : Rat := ((107000619 : Rat) / 40000000)
def block071S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block071V (y : ℝ) : ℝ :=
  ratPotential block071W1 block071W2 block071W3 block071W4 block071S1 block071S2 block071S3 block071S4 y

def block071LeftParamsCertificate : Bool :=
  allBoxesSameParams block071LeftBoxes block071W1 block071W2 block071W3 block071W4 block071S1 block071S2 block071S3 block071S4

theorem block071LeftParamsCertificate_eq_true :
    block071LeftParamsCertificate = true := by
  native_decide

theorem block071_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block071LeftL : ℝ) (block071LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block071S1 : ℝ))
    (hy2ne : y ≠ (block071S2 : ℝ))
    (hy3ne : y ≠ (block071S3 : ℝ))
    (hy4ne : y ≠ (block071S4 : ℝ)) :
    0 < block071V y := by
  have hcert := block071LeftCertificate_eq_true
  unfold block071LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block071LeftBoxes) (lo := block071LeftL) (hi := block071LeftR)
    (w1 := block071W1) (w2 := block071W2) (w3 := block071W3) (w4 := block071W4)
    (s1 := block071S1) (s2 := block071S2) (s3 := block071S3) (s4 := block071S4)
    hboxes hcover block071LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block071RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block071RightChunk000 block071W1 block071W2 block071W3 block071W4 block071S1 block071S2 block071S3 block071S4

theorem block071RightChunk000ParamsCertificate_eq_true :
    block071RightChunk000ParamsCertificate = true := by
  native_decide

theorem block071_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block071RightChunk000L : ℝ) (block071RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block071S1 : ℝ))
    (hy2ne : y ≠ (block071S2 : ℝ))
    (hy3ne : y ≠ (block071S3 : ℝ))
    (hy4ne : y ≠ (block071S4 : ℝ)) :
    0 < block071V y := by
  have hcert := block071RightChunk000Certificate_eq_true
  unfold block071RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block071RightChunk000) (lo := block071RightChunk000L) (hi := block071RightChunk000R)
    (w1 := block071W1) (w2 := block071W2) (w3 := block071W3) (w4 := block071W4)
    (s1 := block071S1) (s2 := block071S2) (s3 := block071S3) (s4 := block071S4)
    hboxes hcover block071RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block071_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block071RightL : ℝ) (block071RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block071S1 : ℝ))
    (hy2ne : y ≠ (block071S2 : ℝ))
    (hy3ne : y ≠ (block071S3 : ℝ))
    (hy4ne : y ≠ (block071S4 : ℝ)) :
    0 < block071V y := by
  have hL : (block071RightChunk000L : ℝ) = (block071RightL : ℝ) := by
    norm_num [block071RightChunk000L, block071RightL]
  have hR : (block071RightChunk000R : ℝ) = (block071RightR : ℝ) := by
    norm_num [block071RightChunk000R, block071RightR]
  have hyc : y ∈ Icc (block071RightChunk000L : ℝ) (block071RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block071_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block071_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block071LeftL : ℝ) (block071LeftR : ℝ) →
    y ≠ 0 → y ≠ (block071S1 : ℝ) → y ≠ (block071S2 : ℝ) →
    y ≠ (block071S3 : ℝ) → y ≠ (block071S4 : ℝ) → 0 < block071V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block071RightL : ℝ) (block071RightR : ℝ) →
    y ≠ 0 → y ≠ (block071S1 : ℝ) → y ≠ (block071S2 : ℝ) →
    y ≠ (block071S3 : ℝ) → y ≠ (block071S4 : ℝ) → 0 < block071V y)

theorem block071_reallog_certificate_proof :
    block071_reallog_certificate := by
  exact ⟨block071_left_V_pos, block071_right_V_pos⟩

end Block071
end M1817475
end Erdos1038Lean
