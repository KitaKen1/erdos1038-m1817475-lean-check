import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block504

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block504

open Set

def block504W1 : Rat := ((2821289429302001 : Rat) / 6250000000000000)
def block504W2 : Rat := (0 : Rat)
def block504W3 : Rat := ((42315800340289317 : Rat) / 100000000000000000)
def block504W4 : Rat := ((2952860098871363 : Rat) / 200000000000000000)
def block504S1 : Rat := ((18174751 : Rat) / 10000000)
def block504S2 : Rat := ((511587 : Rat) / 200000)
def block504S3 : Rat := ((26056161446428571459 : Rat) / 10000000000000000000)
def block504S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block504V (y : ℝ) : ℝ :=
  ratPotential block504W1 block504W2 block504W3 block504W4 block504S1 block504S2 block504S3 block504S4 y

def block504LeftParamsCertificate : Bool :=
  allBoxesSameParams block504LeftBoxes block504W1 block504W2 block504W3 block504W4 block504S1 block504S2 block504S3 block504S4

theorem block504LeftParamsCertificate_eq_true :
    block504LeftParamsCertificate = true := by
  native_decide

theorem block504_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block504LeftL : ℝ) (block504LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block504S1 : ℝ))
    (hy2ne : y ≠ (block504S2 : ℝ))
    (hy3ne : y ≠ (block504S3 : ℝ))
    (hy4ne : y ≠ (block504S4 : ℝ)) :
    0 < block504V y := by
  have hcert := block504LeftCertificate_eq_true
  unfold block504LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block504LeftBoxes) (lo := block504LeftL) (hi := block504LeftR)
    (w1 := block504W1) (w2 := block504W2) (w3 := block504W3) (w4 := block504W4)
    (s1 := block504S1) (s2 := block504S2) (s3 := block504S3) (s4 := block504S4)
    hboxes hcover block504LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block504RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block504RightChunk000 block504W1 block504W2 block504W3 block504W4 block504S1 block504S2 block504S3 block504S4

theorem block504RightChunk000ParamsCertificate_eq_true :
    block504RightChunk000ParamsCertificate = true := by
  native_decide

theorem block504_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block504RightChunk000L : ℝ) (block504RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block504S1 : ℝ))
    (hy2ne : y ≠ (block504S2 : ℝ))
    (hy3ne : y ≠ (block504S3 : ℝ))
    (hy4ne : y ≠ (block504S4 : ℝ)) :
    0 < block504V y := by
  have hcert := block504RightChunk000Certificate_eq_true
  unfold block504RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block504RightChunk000) (lo := block504RightChunk000L) (hi := block504RightChunk000R)
    (w1 := block504W1) (w2 := block504W2) (w3 := block504W3) (w4 := block504W4)
    (s1 := block504S1) (s2 := block504S2) (s3 := block504S3) (s4 := block504S4)
    hboxes hcover block504RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block504_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block504RightL : ℝ) (block504RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block504S1 : ℝ))
    (hy2ne : y ≠ (block504S2 : ℝ))
    (hy3ne : y ≠ (block504S3 : ℝ))
    (hy4ne : y ≠ (block504S4 : ℝ)) :
    0 < block504V y := by
  have hL : (block504RightChunk000L : ℝ) = (block504RightL : ℝ) := by
    norm_num [block504RightChunk000L, block504RightL]
  have hR : (block504RightChunk000R : ℝ) = (block504RightR : ℝ) := by
    norm_num [block504RightChunk000R, block504RightR]
  have hyc : y ∈ Icc (block504RightChunk000L : ℝ) (block504RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block504_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block504_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block504LeftL : ℝ) (block504LeftR : ℝ) →
    y ≠ 0 → y ≠ (block504S1 : ℝ) → y ≠ (block504S2 : ℝ) →
    y ≠ (block504S3 : ℝ) → y ≠ (block504S4 : ℝ) → 0 < block504V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block504RightL : ℝ) (block504RightR : ℝ) →
    y ≠ 0 → y ≠ (block504S1 : ℝ) → y ≠ (block504S2 : ℝ) →
    y ≠ (block504S3 : ℝ) → y ≠ (block504S4 : ℝ) → 0 < block504V y)

theorem block504_reallog_certificate_proof :
    block504_reallog_certificate := by
  exact ⟨block504_left_V_pos, block504_right_V_pos⟩

end Block504
end M1817475
end Erdos1038Lean
