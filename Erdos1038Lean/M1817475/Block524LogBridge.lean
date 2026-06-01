import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block524

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block524

open Set

def block524W1 : Rat := ((207044437175123 : Rat) / 500000000000000)
def block524W2 : Rat := (0 : Rat)
def block524W3 : Rat := ((22495924840076223 : Rat) / 50000000000000000)
def block524W4 : Rat := (0 : Rat)
def block524S1 : Rat := ((18174751 : Rat) / 10000000)
def block524S2 : Rat := ((511587 : Rat) / 200000)
def block524S3 : Rat := ((25977965017857142891 : Rat) / 10000000000000000000)
def block524S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block524V (y : ℝ) : ℝ :=
  ratPotential block524W1 block524W2 block524W3 block524W4 block524S1 block524S2 block524S3 block524S4 y

def block524LeftParamsCertificate : Bool :=
  allBoxesSameParams block524LeftBoxes block524W1 block524W2 block524W3 block524W4 block524S1 block524S2 block524S3 block524S4

theorem block524LeftParamsCertificate_eq_true :
    block524LeftParamsCertificate = true := by
  native_decide

theorem block524_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block524LeftL : ℝ) (block524LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block524S1 : ℝ))
    (hy2ne : y ≠ (block524S2 : ℝ))
    (hy3ne : y ≠ (block524S3 : ℝ))
    (hy4ne : y ≠ (block524S4 : ℝ)) :
    0 < block524V y := by
  have hcert := block524LeftCertificate_eq_true
  unfold block524LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block524LeftBoxes) (lo := block524LeftL) (hi := block524LeftR)
    (w1 := block524W1) (w2 := block524W2) (w3 := block524W3) (w4 := block524W4)
    (s1 := block524S1) (s2 := block524S2) (s3 := block524S3) (s4 := block524S4)
    hboxes hcover block524LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block524RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block524RightChunk000 block524W1 block524W2 block524W3 block524W4 block524S1 block524S2 block524S3 block524S4

theorem block524RightChunk000ParamsCertificate_eq_true :
    block524RightChunk000ParamsCertificate = true := by
  native_decide

theorem block524_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block524RightChunk000L : ℝ) (block524RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block524S1 : ℝ))
    (hy2ne : y ≠ (block524S2 : ℝ))
    (hy3ne : y ≠ (block524S3 : ℝ))
    (hy4ne : y ≠ (block524S4 : ℝ)) :
    0 < block524V y := by
  have hcert := block524RightChunk000Certificate_eq_true
  unfold block524RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block524RightChunk000) (lo := block524RightChunk000L) (hi := block524RightChunk000R)
    (w1 := block524W1) (w2 := block524W2) (w3 := block524W3) (w4 := block524W4)
    (s1 := block524S1) (s2 := block524S2) (s3 := block524S3) (s4 := block524S4)
    hboxes hcover block524RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block524_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block524RightL : ℝ) (block524RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block524S1 : ℝ))
    (hy2ne : y ≠ (block524S2 : ℝ))
    (hy3ne : y ≠ (block524S3 : ℝ))
    (hy4ne : y ≠ (block524S4 : ℝ)) :
    0 < block524V y := by
  have hL : (block524RightChunk000L : ℝ) = (block524RightL : ℝ) := by
    norm_num [block524RightChunk000L, block524RightL]
  have hR : (block524RightChunk000R : ℝ) = (block524RightR : ℝ) := by
    norm_num [block524RightChunk000R, block524RightR]
  have hyc : y ∈ Icc (block524RightChunk000L : ℝ) (block524RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block524_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block524_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block524LeftL : ℝ) (block524LeftR : ℝ) →
    y ≠ 0 → y ≠ (block524S1 : ℝ) → y ≠ (block524S2 : ℝ) →
    y ≠ (block524S3 : ℝ) → y ≠ (block524S4 : ℝ) → 0 < block524V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block524RightL : ℝ) (block524RightR : ℝ) →
    y ≠ 0 → y ≠ (block524S1 : ℝ) → y ≠ (block524S2 : ℝ) →
    y ≠ (block524S3 : ℝ) → y ≠ (block524S4 : ℝ) → 0 < block524V y)

theorem block524_reallog_certificate_proof :
    block524_reallog_certificate := by
  exact ⟨block524_left_V_pos, block524_right_V_pos⟩

end Block524
end M1817475
end Erdos1038Lean
