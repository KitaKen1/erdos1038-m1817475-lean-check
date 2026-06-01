import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block428

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block428

open Set

def block428W1 : Rat := ((1324868391572421 : Rat) / 2000000000000000)
def block428W2 : Rat := (0 : Rat)
def block428W3 : Rat := ((1527748143120453 : Rat) / 5000000000000000)
def block428W4 : Rat := ((323735743036401 : Rat) / 4000000000000000)
def block428S1 : Rat := ((18174751 : Rat) / 10000000)
def block428S2 : Rat := ((511587 : Rat) / 200000)
def block428S3 : Rat := ((131766539375000000087 : Rat) / 50000000000000000000)
def block428S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block428V (y : ℝ) : ℝ :=
  ratPotential block428W1 block428W2 block428W3 block428W4 block428S1 block428S2 block428S3 block428S4 y

def block428LeftParamsCertificate : Bool :=
  allBoxesSameParams block428LeftBoxes block428W1 block428W2 block428W3 block428W4 block428S1 block428S2 block428S3 block428S4

theorem block428LeftParamsCertificate_eq_true :
    block428LeftParamsCertificate = true := by
  native_decide

theorem block428_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block428LeftL : ℝ) (block428LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block428S1 : ℝ))
    (hy2ne : y ≠ (block428S2 : ℝ))
    (hy3ne : y ≠ (block428S3 : ℝ))
    (hy4ne : y ≠ (block428S4 : ℝ)) :
    0 < block428V y := by
  have hcert := block428LeftCertificate_eq_true
  unfold block428LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block428LeftBoxes) (lo := block428LeftL) (hi := block428LeftR)
    (w1 := block428W1) (w2 := block428W2) (w3 := block428W3) (w4 := block428W4)
    (s1 := block428S1) (s2 := block428S2) (s3 := block428S3) (s4 := block428S4)
    hboxes hcover block428LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block428RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block428RightChunk000 block428W1 block428W2 block428W3 block428W4 block428S1 block428S2 block428S3 block428S4

theorem block428RightChunk000ParamsCertificate_eq_true :
    block428RightChunk000ParamsCertificate = true := by
  native_decide

theorem block428_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block428RightChunk000L : ℝ) (block428RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block428S1 : ℝ))
    (hy2ne : y ≠ (block428S2 : ℝ))
    (hy3ne : y ≠ (block428S3 : ℝ))
    (hy4ne : y ≠ (block428S4 : ℝ)) :
    0 < block428V y := by
  have hcert := block428RightChunk000Certificate_eq_true
  unfold block428RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block428RightChunk000) (lo := block428RightChunk000L) (hi := block428RightChunk000R)
    (w1 := block428W1) (w2 := block428W2) (w3 := block428W3) (w4 := block428W4)
    (s1 := block428S1) (s2 := block428S2) (s3 := block428S3) (s4 := block428S4)
    hboxes hcover block428RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block428_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block428RightL : ℝ) (block428RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block428S1 : ℝ))
    (hy2ne : y ≠ (block428S2 : ℝ))
    (hy3ne : y ≠ (block428S3 : ℝ))
    (hy4ne : y ≠ (block428S4 : ℝ)) :
    0 < block428V y := by
  have hL : (block428RightChunk000L : ℝ) = (block428RightL : ℝ) := by
    norm_num [block428RightChunk000L, block428RightL]
  have hR : (block428RightChunk000R : ℝ) = (block428RightR : ℝ) := by
    norm_num [block428RightChunk000R, block428RightR]
  have hyc : y ∈ Icc (block428RightChunk000L : ℝ) (block428RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block428_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block428_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block428LeftL : ℝ) (block428LeftR : ℝ) →
    y ≠ 0 → y ≠ (block428S1 : ℝ) → y ≠ (block428S2 : ℝ) →
    y ≠ (block428S3 : ℝ) → y ≠ (block428S4 : ℝ) → 0 < block428V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block428RightL : ℝ) (block428RightR : ℝ) →
    y ≠ 0 → y ≠ (block428S1 : ℝ) → y ≠ (block428S2 : ℝ) →
    y ≠ (block428S3 : ℝ) → y ≠ (block428S4 : ℝ) → 0 < block428V y)

theorem block428_reallog_certificate_proof :
    block428_reallog_certificate := by
  exact ⟨block428_left_V_pos, block428_right_V_pos⟩

end Block428
end M1817475
end Erdos1038Lean
