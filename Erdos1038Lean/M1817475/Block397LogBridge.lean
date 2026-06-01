import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block397

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block397

open Set

def block397W1 : Rat := ((1408272880156383 : Rat) / 2000000000000000)
def block397W2 : Rat := (0 : Rat)
def block397W3 : Rat := ((3743017755914567 : Rat) / 10000000000000000)
def block397W4 : Rat := (0 : Rat)
def block397S1 : Rat := ((18174751 : Rat) / 10000000)
def block397S2 : Rat := ((511587 : Rat) / 200000)
def block397S3 : Rat := ((133095878660714285743 : Rat) / 50000000000000000000)
def block397S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block397V (y : ℝ) : ℝ :=
  ratPotential block397W1 block397W2 block397W3 block397W4 block397S1 block397S2 block397S3 block397S4 y

def block397LeftParamsCertificate : Bool :=
  allBoxesSameParams block397LeftBoxes block397W1 block397W2 block397W3 block397W4 block397S1 block397S2 block397S3 block397S4

theorem block397LeftParamsCertificate_eq_true :
    block397LeftParamsCertificate = true := by
  native_decide

theorem block397_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block397LeftL : ℝ) (block397LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block397S1 : ℝ))
    (hy2ne : y ≠ (block397S2 : ℝ))
    (hy3ne : y ≠ (block397S3 : ℝ))
    (hy4ne : y ≠ (block397S4 : ℝ)) :
    0 < block397V y := by
  have hcert := block397LeftCertificate_eq_true
  unfold block397LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block397LeftBoxes) (lo := block397LeftL) (hi := block397LeftR)
    (w1 := block397W1) (w2 := block397W2) (w3 := block397W3) (w4 := block397W4)
    (s1 := block397S1) (s2 := block397S2) (s3 := block397S3) (s4 := block397S4)
    hboxes hcover block397LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block397RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block397RightChunk000 block397W1 block397W2 block397W3 block397W4 block397S1 block397S2 block397S3 block397S4

theorem block397RightChunk000ParamsCertificate_eq_true :
    block397RightChunk000ParamsCertificate = true := by
  native_decide

theorem block397_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block397RightChunk000L : ℝ) (block397RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block397S1 : ℝ))
    (hy2ne : y ≠ (block397S2 : ℝ))
    (hy3ne : y ≠ (block397S3 : ℝ))
    (hy4ne : y ≠ (block397S4 : ℝ)) :
    0 < block397V y := by
  have hcert := block397RightChunk000Certificate_eq_true
  unfold block397RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block397RightChunk000) (lo := block397RightChunk000L) (hi := block397RightChunk000R)
    (w1 := block397W1) (w2 := block397W2) (w3 := block397W3) (w4 := block397W4)
    (s1 := block397S1) (s2 := block397S2) (s3 := block397S3) (s4 := block397S4)
    hboxes hcover block397RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block397_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block397RightL : ℝ) (block397RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block397S1 : ℝ))
    (hy2ne : y ≠ (block397S2 : ℝ))
    (hy3ne : y ≠ (block397S3 : ℝ))
    (hy4ne : y ≠ (block397S4 : ℝ)) :
    0 < block397V y := by
  have hL : (block397RightChunk000L : ℝ) = (block397RightL : ℝ) := by
    norm_num [block397RightChunk000L, block397RightL]
  have hR : (block397RightChunk000R : ℝ) = (block397RightR : ℝ) := by
    norm_num [block397RightChunk000R, block397RightR]
  have hyc : y ∈ Icc (block397RightChunk000L : ℝ) (block397RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block397_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block397_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block397LeftL : ℝ) (block397LeftR : ℝ) →
    y ≠ 0 → y ≠ (block397S1 : ℝ) → y ≠ (block397S2 : ℝ) →
    y ≠ (block397S3 : ℝ) → y ≠ (block397S4 : ℝ) → 0 < block397V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block397RightL : ℝ) (block397RightR : ℝ) →
    y ≠ 0 → y ≠ (block397S1 : ℝ) → y ≠ (block397S2 : ℝ) →
    y ≠ (block397S3 : ℝ) → y ≠ (block397S4 : ℝ) → 0 < block397V y)

theorem block397_reallog_certificate_proof :
    block397_reallog_certificate := by
  exact ⟨block397_left_V_pos, block397_right_V_pos⟩

end Block397
end M1817475
end Erdos1038Lean
