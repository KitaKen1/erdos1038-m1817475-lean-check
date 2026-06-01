import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block127

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block127

open Set

def block127W1 : Rat := ((256321152743291 : Rat) / 100000000000000)
def block127W2 : Rat := (0 : Rat)
def block127W3 : Rat := ((5049234263098227 : Rat) / 50000000000000000)
def block127W4 : Rat := ((14124360485208187 : Rat) / 100000000000000000)
def block127S1 : Rat := ((18174751 : Rat) / 10000000)
def block127S2 : Rat := ((511587 : Rat) / 200000)
def block127S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block127S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block127V (y : ℝ) : ℝ :=
  ratPotential block127W1 block127W2 block127W3 block127W4 block127S1 block127S2 block127S3 block127S4 y

def block127LeftParamsCertificate : Bool :=
  allBoxesSameParams block127LeftBoxes block127W1 block127W2 block127W3 block127W4 block127S1 block127S2 block127S3 block127S4

theorem block127LeftParamsCertificate_eq_true :
    block127LeftParamsCertificate = true := by
  native_decide

theorem block127_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block127LeftL : ℝ) (block127LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block127S1 : ℝ))
    (hy2ne : y ≠ (block127S2 : ℝ))
    (hy3ne : y ≠ (block127S3 : ℝ))
    (hy4ne : y ≠ (block127S4 : ℝ)) :
    0 < block127V y := by
  have hcert := block127LeftCertificate_eq_true
  unfold block127LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block127LeftBoxes) (lo := block127LeftL) (hi := block127LeftR)
    (w1 := block127W1) (w2 := block127W2) (w3 := block127W3) (w4 := block127W4)
    (s1 := block127S1) (s2 := block127S2) (s3 := block127S3) (s4 := block127S4)
    hboxes hcover block127LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block127RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block127RightChunk000 block127W1 block127W2 block127W3 block127W4 block127S1 block127S2 block127S3 block127S4

theorem block127RightChunk000ParamsCertificate_eq_true :
    block127RightChunk000ParamsCertificate = true := by
  native_decide

theorem block127_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block127RightChunk000L : ℝ) (block127RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block127S1 : ℝ))
    (hy2ne : y ≠ (block127S2 : ℝ))
    (hy3ne : y ≠ (block127S3 : ℝ))
    (hy4ne : y ≠ (block127S4 : ℝ)) :
    0 < block127V y := by
  have hcert := block127RightChunk000Certificate_eq_true
  unfold block127RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block127RightChunk000) (lo := block127RightChunk000L) (hi := block127RightChunk000R)
    (w1 := block127W1) (w2 := block127W2) (w3 := block127W3) (w4 := block127W4)
    (s1 := block127S1) (s2 := block127S2) (s3 := block127S3) (s4 := block127S4)
    hboxes hcover block127RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block127_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block127RightL : ℝ) (block127RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block127S1 : ℝ))
    (hy2ne : y ≠ (block127S2 : ℝ))
    (hy3ne : y ≠ (block127S3 : ℝ))
    (hy4ne : y ≠ (block127S4 : ℝ)) :
    0 < block127V y := by
  have hL : (block127RightChunk000L : ℝ) = (block127RightL : ℝ) := by
    norm_num [block127RightChunk000L, block127RightL]
  have hR : (block127RightChunk000R : ℝ) = (block127RightR : ℝ) := by
    norm_num [block127RightChunk000R, block127RightR]
  have hyc : y ∈ Icc (block127RightChunk000L : ℝ) (block127RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block127_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block127_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block127LeftL : ℝ) (block127LeftR : ℝ) →
    y ≠ 0 → y ≠ (block127S1 : ℝ) → y ≠ (block127S2 : ℝ) →
    y ≠ (block127S3 : ℝ) → y ≠ (block127S4 : ℝ) → 0 < block127V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block127RightL : ℝ) (block127RightR : ℝ) →
    y ≠ 0 → y ≠ (block127S1 : ℝ) → y ≠ (block127S2 : ℝ) →
    y ≠ (block127S3 : ℝ) → y ≠ (block127S4 : ℝ) → 0 < block127V y)

theorem block127_reallog_certificate_proof :
    block127_reallog_certificate := by
  exact ⟨block127_left_V_pos, block127_right_V_pos⟩

end Block127
end M1817475
end Erdos1038Lean
