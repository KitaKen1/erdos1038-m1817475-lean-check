import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block099

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block099

open Set

def block099W1 : Rat := ((26200641958995403 : Rat) / 10000000000000000)
def block099W2 : Rat := (0 : Rat)
def block099W3 : Rat := ((4766834635126133 : Rat) / 100000000000000000)
def block099W4 : Rat := ((80249187447033 : Rat) / 400000000000000)
def block099S1 : Rat := ((18174751 : Rat) / 10000000)
def block099S2 : Rat := ((511587 : Rat) / 200000)
def block099S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block099S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block099V (y : ℝ) : ℝ :=
  ratPotential block099W1 block099W2 block099W3 block099W4 block099S1 block099S2 block099S3 block099S4 y

def block099LeftParamsCertificate : Bool :=
  allBoxesSameParams block099LeftBoxes block099W1 block099W2 block099W3 block099W4 block099S1 block099S2 block099S3 block099S4

theorem block099LeftParamsCertificate_eq_true :
    block099LeftParamsCertificate = true := by
  native_decide

theorem block099_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block099LeftL : ℝ) (block099LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block099S1 : ℝ))
    (hy2ne : y ≠ (block099S2 : ℝ))
    (hy3ne : y ≠ (block099S3 : ℝ))
    (hy4ne : y ≠ (block099S4 : ℝ)) :
    0 < block099V y := by
  have hcert := block099LeftCertificate_eq_true
  unfold block099LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block099LeftBoxes) (lo := block099LeftL) (hi := block099LeftR)
    (w1 := block099W1) (w2 := block099W2) (w3 := block099W3) (w4 := block099W4)
    (s1 := block099S1) (s2 := block099S2) (s3 := block099S3) (s4 := block099S4)
    hboxes hcover block099LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block099RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block099RightChunk000 block099W1 block099W2 block099W3 block099W4 block099S1 block099S2 block099S3 block099S4

theorem block099RightChunk000ParamsCertificate_eq_true :
    block099RightChunk000ParamsCertificate = true := by
  native_decide

theorem block099_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block099RightChunk000L : ℝ) (block099RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block099S1 : ℝ))
    (hy2ne : y ≠ (block099S2 : ℝ))
    (hy3ne : y ≠ (block099S3 : ℝ))
    (hy4ne : y ≠ (block099S4 : ℝ)) :
    0 < block099V y := by
  have hcert := block099RightChunk000Certificate_eq_true
  unfold block099RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block099RightChunk000) (lo := block099RightChunk000L) (hi := block099RightChunk000R)
    (w1 := block099W1) (w2 := block099W2) (w3 := block099W3) (w4 := block099W4)
    (s1 := block099S1) (s2 := block099S2) (s3 := block099S3) (s4 := block099S4)
    hboxes hcover block099RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block099_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block099RightL : ℝ) (block099RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block099S1 : ℝ))
    (hy2ne : y ≠ (block099S2 : ℝ))
    (hy3ne : y ≠ (block099S3 : ℝ))
    (hy4ne : y ≠ (block099S4 : ℝ)) :
    0 < block099V y := by
  have hL : (block099RightChunk000L : ℝ) = (block099RightL : ℝ) := by
    norm_num [block099RightChunk000L, block099RightL]
  have hR : (block099RightChunk000R : ℝ) = (block099RightR : ℝ) := by
    norm_num [block099RightChunk000R, block099RightR]
  have hyc : y ∈ Icc (block099RightChunk000L : ℝ) (block099RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block099_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block099_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block099LeftL : ℝ) (block099LeftR : ℝ) →
    y ≠ 0 → y ≠ (block099S1 : ℝ) → y ≠ (block099S2 : ℝ) →
    y ≠ (block099S3 : ℝ) → y ≠ (block099S4 : ℝ) → 0 < block099V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block099RightL : ℝ) (block099RightR : ℝ) →
    y ≠ 0 → y ≠ (block099S1 : ℝ) → y ≠ (block099S2 : ℝ) →
    y ≠ (block099S3 : ℝ) → y ≠ (block099S4 : ℝ) → 0 < block099V y)

theorem block099_reallog_certificate_proof :
    block099_reallog_certificate := by
  exact ⟨block099_left_V_pos, block099_right_V_pos⟩

end Block099
end M1817475
end Erdos1038Lean
