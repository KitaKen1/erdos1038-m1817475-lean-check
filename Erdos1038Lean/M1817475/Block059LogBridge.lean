import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block059

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block059

open Set

def block059W1 : Rat := ((2843769382175007 : Rat) / 1000000000000000)
def block059W2 : Rat := (0 : Rat)
def block059W3 : Rat := (0 : Rat)
def block059W4 : Rat := ((6528790667005241 : Rat) / 25000000000000000)
def block059S1 : Rat := ((18174751 : Rat) / 10000000)
def block059S2 : Rat := ((511587 : Rat) / 200000)
def block059S3 : Rat := ((107000619 : Rat) / 40000000)
def block059S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block059V (y : ℝ) : ℝ :=
  ratPotential block059W1 block059W2 block059W3 block059W4 block059S1 block059S2 block059S3 block059S4 y

def block059LeftParamsCertificate : Bool :=
  allBoxesSameParams block059LeftBoxes block059W1 block059W2 block059W3 block059W4 block059S1 block059S2 block059S3 block059S4

theorem block059LeftParamsCertificate_eq_true :
    block059LeftParamsCertificate = true := by
  native_decide

theorem block059_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block059LeftL : ℝ) (block059LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block059S1 : ℝ))
    (hy2ne : y ≠ (block059S2 : ℝ))
    (hy3ne : y ≠ (block059S3 : ℝ))
    (hy4ne : y ≠ (block059S4 : ℝ)) :
    0 < block059V y := by
  have hcert := block059LeftCertificate_eq_true
  unfold block059LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block059LeftBoxes) (lo := block059LeftL) (hi := block059LeftR)
    (w1 := block059W1) (w2 := block059W2) (w3 := block059W3) (w4 := block059W4)
    (s1 := block059S1) (s2 := block059S2) (s3 := block059S3) (s4 := block059S4)
    hboxes hcover block059LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block059RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block059RightChunk000 block059W1 block059W2 block059W3 block059W4 block059S1 block059S2 block059S3 block059S4

theorem block059RightChunk000ParamsCertificate_eq_true :
    block059RightChunk000ParamsCertificate = true := by
  native_decide

theorem block059_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block059RightChunk000L : ℝ) (block059RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block059S1 : ℝ))
    (hy2ne : y ≠ (block059S2 : ℝ))
    (hy3ne : y ≠ (block059S3 : ℝ))
    (hy4ne : y ≠ (block059S4 : ℝ)) :
    0 < block059V y := by
  have hcert := block059RightChunk000Certificate_eq_true
  unfold block059RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block059RightChunk000) (lo := block059RightChunk000L) (hi := block059RightChunk000R)
    (w1 := block059W1) (w2 := block059W2) (w3 := block059W3) (w4 := block059W4)
    (s1 := block059S1) (s2 := block059S2) (s3 := block059S3) (s4 := block059S4)
    hboxes hcover block059RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block059_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block059RightL : ℝ) (block059RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block059S1 : ℝ))
    (hy2ne : y ≠ (block059S2 : ℝ))
    (hy3ne : y ≠ (block059S3 : ℝ))
    (hy4ne : y ≠ (block059S4 : ℝ)) :
    0 < block059V y := by
  have hL : (block059RightChunk000L : ℝ) = (block059RightL : ℝ) := by
    norm_num [block059RightChunk000L, block059RightL]
  have hR : (block059RightChunk000R : ℝ) = (block059RightR : ℝ) := by
    norm_num [block059RightChunk000R, block059RightR]
  have hyc : y ∈ Icc (block059RightChunk000L : ℝ) (block059RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block059_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block059_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block059LeftL : ℝ) (block059LeftR : ℝ) →
    y ≠ 0 → y ≠ (block059S1 : ℝ) → y ≠ (block059S2 : ℝ) →
    y ≠ (block059S3 : ℝ) → y ≠ (block059S4 : ℝ) → 0 < block059V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block059RightL : ℝ) (block059RightR : ℝ) →
    y ≠ 0 → y ≠ (block059S1 : ℝ) → y ≠ (block059S2 : ℝ) →
    y ≠ (block059S3 : ℝ) → y ≠ (block059S4 : ℝ) → 0 < block059V y)

theorem block059_reallog_certificate_proof :
    block059_reallog_certificate := by
  exact ⟨block059_left_V_pos, block059_right_V_pos⟩

end Block059
end M1817475
end Erdos1038Lean
