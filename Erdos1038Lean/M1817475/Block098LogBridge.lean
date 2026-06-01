import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block098

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block098

open Set

def block098W1 : Rat := ((209978802148133 : Rat) / 80000000000000)
def block098W2 : Rat := (0 : Rat)
def block098W3 : Rat := ((23183677986940557 : Rat) / 500000000000000000)
def block098W4 : Rat := ((20220363225649549 : Rat) / 100000000000000000)
def block098S1 : Rat := ((18174751 : Rat) / 10000000)
def block098S2 : Rat := ((511587 : Rat) / 200000)
def block098S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block098S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block098V (y : ℝ) : ℝ :=
  ratPotential block098W1 block098W2 block098W3 block098W4 block098S1 block098S2 block098S3 block098S4 y

def block098LeftParamsCertificate : Bool :=
  allBoxesSameParams block098LeftBoxes block098W1 block098W2 block098W3 block098W4 block098S1 block098S2 block098S3 block098S4

theorem block098LeftParamsCertificate_eq_true :
    block098LeftParamsCertificate = true := by
  native_decide

theorem block098_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block098LeftL : ℝ) (block098LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block098S1 : ℝ))
    (hy2ne : y ≠ (block098S2 : ℝ))
    (hy3ne : y ≠ (block098S3 : ℝ))
    (hy4ne : y ≠ (block098S4 : ℝ)) :
    0 < block098V y := by
  have hcert := block098LeftCertificate_eq_true
  unfold block098LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block098LeftBoxes) (lo := block098LeftL) (hi := block098LeftR)
    (w1 := block098W1) (w2 := block098W2) (w3 := block098W3) (w4 := block098W4)
    (s1 := block098S1) (s2 := block098S2) (s3 := block098S3) (s4 := block098S4)
    hboxes hcover block098LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block098RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block098RightChunk000 block098W1 block098W2 block098W3 block098W4 block098S1 block098S2 block098S3 block098S4

theorem block098RightChunk000ParamsCertificate_eq_true :
    block098RightChunk000ParamsCertificate = true := by
  native_decide

theorem block098_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block098RightChunk000L : ℝ) (block098RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block098S1 : ℝ))
    (hy2ne : y ≠ (block098S2 : ℝ))
    (hy3ne : y ≠ (block098S3 : ℝ))
    (hy4ne : y ≠ (block098S4 : ℝ)) :
    0 < block098V y := by
  have hcert := block098RightChunk000Certificate_eq_true
  unfold block098RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block098RightChunk000) (lo := block098RightChunk000L) (hi := block098RightChunk000R)
    (w1 := block098W1) (w2 := block098W2) (w3 := block098W3) (w4 := block098W4)
    (s1 := block098S1) (s2 := block098S2) (s3 := block098S3) (s4 := block098S4)
    hboxes hcover block098RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block098_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block098RightL : ℝ) (block098RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block098S1 : ℝ))
    (hy2ne : y ≠ (block098S2 : ℝ))
    (hy3ne : y ≠ (block098S3 : ℝ))
    (hy4ne : y ≠ (block098S4 : ℝ)) :
    0 < block098V y := by
  have hL : (block098RightChunk000L : ℝ) = (block098RightL : ℝ) := by
    norm_num [block098RightChunk000L, block098RightL]
  have hR : (block098RightChunk000R : ℝ) = (block098RightR : ℝ) := by
    norm_num [block098RightChunk000R, block098RightR]
  have hyc : y ∈ Icc (block098RightChunk000L : ℝ) (block098RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block098_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block098_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block098LeftL : ℝ) (block098LeftR : ℝ) →
    y ≠ 0 → y ≠ (block098S1 : ℝ) → y ≠ (block098S2 : ℝ) →
    y ≠ (block098S3 : ℝ) → y ≠ (block098S4 : ℝ) → 0 < block098V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block098RightL : ℝ) (block098RightR : ℝ) →
    y ≠ 0 → y ≠ (block098S1 : ℝ) → y ≠ (block098S2 : ℝ) →
    y ≠ (block098S3 : ℝ) → y ≠ (block098S4 : ℝ) → 0 < block098V y)

theorem block098_reallog_certificate_proof :
    block098_reallog_certificate := by
  exact ⟨block098_left_V_pos, block098_right_V_pos⟩

end Block098
end M1817475
end Erdos1038Lean
