import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block009

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block009

open Set

def block009W1 : Rat := ((4969505860891833 : Rat) / 500000000000000)
def block009W2 : Rat := (0 : Rat)
def block009W3 : Rat := (0 : Rat)
def block009W4 : Rat := ((12596375539739013 : Rat) / 50000000000000000)
def block009S1 : Rat := ((18174751 : Rat) / 10000000)
def block009S2 : Rat := ((511587 : Rat) / 200000)
def block009S3 : Rat := ((107000619 : Rat) / 40000000)
def block009S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block009V (y : ℝ) : ℝ :=
  ratPotential block009W1 block009W2 block009W3 block009W4 block009S1 block009S2 block009S3 block009S4 y

def block009LeftParamsCertificate : Bool :=
  allBoxesSameParams block009LeftBoxes block009W1 block009W2 block009W3 block009W4 block009S1 block009S2 block009S3 block009S4

theorem block009LeftParamsCertificate_eq_true :
    block009LeftParamsCertificate = true := by
  native_decide

theorem block009_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block009LeftL : ℝ) (block009LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block009S1 : ℝ))
    (hy2ne : y ≠ (block009S2 : ℝ))
    (hy3ne : y ≠ (block009S3 : ℝ))
    (hy4ne : y ≠ (block009S4 : ℝ)) :
    0 < block009V y := by
  have hcert := block009LeftCertificate_eq_true
  unfold block009LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block009LeftBoxes) (lo := block009LeftL) (hi := block009LeftR)
    (w1 := block009W1) (w2 := block009W2) (w3 := block009W3) (w4 := block009W4)
    (s1 := block009S1) (s2 := block009S2) (s3 := block009S3) (s4 := block009S4)
    hboxes hcover block009LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block009RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block009RightChunk000 block009W1 block009W2 block009W3 block009W4 block009S1 block009S2 block009S3 block009S4

theorem block009RightChunk000ParamsCertificate_eq_true :
    block009RightChunk000ParamsCertificate = true := by
  native_decide

theorem block009_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block009RightChunk000L : ℝ) (block009RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block009S1 : ℝ))
    (hy2ne : y ≠ (block009S2 : ℝ))
    (hy3ne : y ≠ (block009S3 : ℝ))
    (hy4ne : y ≠ (block009S4 : ℝ)) :
    0 < block009V y := by
  have hcert := block009RightChunk000Certificate_eq_true
  unfold block009RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block009RightChunk000) (lo := block009RightChunk000L) (hi := block009RightChunk000R)
    (w1 := block009W1) (w2 := block009W2) (w3 := block009W3) (w4 := block009W4)
    (s1 := block009S1) (s2 := block009S2) (s3 := block009S3) (s4 := block009S4)
    hboxes hcover block009RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block009_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block009RightL : ℝ) (block009RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block009S1 : ℝ))
    (hy2ne : y ≠ (block009S2 : ℝ))
    (hy3ne : y ≠ (block009S3 : ℝ))
    (hy4ne : y ≠ (block009S4 : ℝ)) :
    0 < block009V y := by
  have hL : (block009RightChunk000L : ℝ) = (block009RightL : ℝ) := by
    norm_num [block009RightChunk000L, block009RightL]
  have hR : (block009RightChunk000R : ℝ) = (block009RightR : ℝ) := by
    norm_num [block009RightChunk000R, block009RightR]
  have hyc : y ∈ Icc (block009RightChunk000L : ℝ) (block009RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block009_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block009_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block009LeftL : ℝ) (block009LeftR : ℝ) →
    y ≠ 0 → y ≠ (block009S1 : ℝ) → y ≠ (block009S2 : ℝ) →
    y ≠ (block009S3 : ℝ) → y ≠ (block009S4 : ℝ) → 0 < block009V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block009RightL : ℝ) (block009RightR : ℝ) →
    y ≠ 0 → y ≠ (block009S1 : ℝ) → y ≠ (block009S2 : ℝ) →
    y ≠ (block009S3 : ℝ) → y ≠ (block009S4 : ℝ) → 0 < block009V y)

theorem block009_reallog_certificate_proof :
    block009_reallog_certificate := by
  exact ⟨block009_left_V_pos, block009_right_V_pos⟩

end Block009
end M1817475
end Erdos1038Lean
