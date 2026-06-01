import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block095

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block095

open Set

def block095W1 : Rat := ((1074749137863177 : Rat) / 500000000000000)
def block095W2 : Rat := (0 : Rat)
def block095W3 : Rat := ((167667847221913 : Rat) / 2500000000000000)
def block095W4 : Rat := ((3941347948802067 : Rat) / 20000000000000000)
def block095S1 : Rat := ((18174751 : Rat) / 10000000)
def block095S2 : Rat := ((511587 : Rat) / 200000)
def block095S3 : Rat := ((135324476874999999931 : Rat) / 50000000000000000000)
def block095S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block095V (y : ℝ) : ℝ :=
  ratPotential block095W1 block095W2 block095W3 block095W4 block095S1 block095S2 block095S3 block095S4 y

def block095LeftParamsCertificate : Bool :=
  allBoxesSameParams block095LeftBoxes block095W1 block095W2 block095W3 block095W4 block095S1 block095S2 block095S3 block095S4

theorem block095LeftParamsCertificate_eq_true :
    block095LeftParamsCertificate = true := by
  native_decide

theorem block095_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block095LeftL : ℝ) (block095LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block095S1 : ℝ))
    (hy2ne : y ≠ (block095S2 : ℝ))
    (hy3ne : y ≠ (block095S3 : ℝ))
    (hy4ne : y ≠ (block095S4 : ℝ)) :
    0 < block095V y := by
  have hcert := block095LeftCertificate_eq_true
  unfold block095LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block095LeftBoxes) (lo := block095LeftL) (hi := block095LeftR)
    (w1 := block095W1) (w2 := block095W2) (w3 := block095W3) (w4 := block095W4)
    (s1 := block095S1) (s2 := block095S2) (s3 := block095S3) (s4 := block095S4)
    hboxes hcover block095LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block095RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block095RightChunk000 block095W1 block095W2 block095W3 block095W4 block095S1 block095S2 block095S3 block095S4

theorem block095RightChunk000ParamsCertificate_eq_true :
    block095RightChunk000ParamsCertificate = true := by
  native_decide

theorem block095_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block095RightChunk000L : ℝ) (block095RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block095S1 : ℝ))
    (hy2ne : y ≠ (block095S2 : ℝ))
    (hy3ne : y ≠ (block095S3 : ℝ))
    (hy4ne : y ≠ (block095S4 : ℝ)) :
    0 < block095V y := by
  have hcert := block095RightChunk000Certificate_eq_true
  unfold block095RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block095RightChunk000) (lo := block095RightChunk000L) (hi := block095RightChunk000R)
    (w1 := block095W1) (w2 := block095W2) (w3 := block095W3) (w4 := block095W4)
    (s1 := block095S1) (s2 := block095S2) (s3 := block095S3) (s4 := block095S4)
    hboxes hcover block095RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block095_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block095RightL : ℝ) (block095RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block095S1 : ℝ))
    (hy2ne : y ≠ (block095S2 : ℝ))
    (hy3ne : y ≠ (block095S3 : ℝ))
    (hy4ne : y ≠ (block095S4 : ℝ)) :
    0 < block095V y := by
  have hL : (block095RightChunk000L : ℝ) = (block095RightL : ℝ) := by
    norm_num [block095RightChunk000L, block095RightL]
  have hR : (block095RightChunk000R : ℝ) = (block095RightR : ℝ) := by
    norm_num [block095RightChunk000R, block095RightR]
  have hyc : y ∈ Icc (block095RightChunk000L : ℝ) (block095RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block095_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block095_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block095LeftL : ℝ) (block095LeftR : ℝ) →
    y ≠ 0 → y ≠ (block095S1 : ℝ) → y ≠ (block095S2 : ℝ) →
    y ≠ (block095S3 : ℝ) → y ≠ (block095S4 : ℝ) → 0 < block095V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block095RightL : ℝ) (block095RightR : ℝ) →
    y ≠ 0 → y ≠ (block095S1 : ℝ) → y ≠ (block095S2 : ℝ) →
    y ≠ (block095S3 : ℝ) → y ≠ (block095S4 : ℝ) → 0 < block095V y)

theorem block095_reallog_certificate_proof :
    block095_reallog_certificate := by
  exact ⟨block095_left_V_pos, block095_right_V_pos⟩

end Block095
end M1817475
end Erdos1038Lean
