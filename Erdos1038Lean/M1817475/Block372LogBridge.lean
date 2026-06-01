import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block372

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block372

open Set

def block372W1 : Rat := ((8639662440929663 : Rat) / 10000000000000000)
def block372W2 : Rat := ((2351514050792649 : Rat) / 50000000000000000)
def block372W3 : Rat := ((1554546337480957 : Rat) / 10000000000000000)
def block372W4 : Rat := ((699479050580669 : Rat) / 5000000000000000)
def block372S1 : Rat := ((18174751 : Rat) / 10000000)
def block372S2 : Rat := ((511587 : Rat) / 200000)
def block372S3 : Rat := ((132861289375000000039 : Rat) / 50000000000000000000)
def block372S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block372V (y : ℝ) : ℝ :=
  ratPotential block372W1 block372W2 block372W3 block372W4 block372S1 block372S2 block372S3 block372S4 y

def block372LeftParamsCertificate : Bool :=
  allBoxesSameParams block372LeftBoxes block372W1 block372W2 block372W3 block372W4 block372S1 block372S2 block372S3 block372S4

theorem block372LeftParamsCertificate_eq_true :
    block372LeftParamsCertificate = true := by
  native_decide

theorem block372_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block372LeftL : ℝ) (block372LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block372S1 : ℝ))
    (hy2ne : y ≠ (block372S2 : ℝ))
    (hy3ne : y ≠ (block372S3 : ℝ))
    (hy4ne : y ≠ (block372S4 : ℝ)) :
    0 < block372V y := by
  have hcert := block372LeftCertificate_eq_true
  unfold block372LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block372LeftBoxes) (lo := block372LeftL) (hi := block372LeftR)
    (w1 := block372W1) (w2 := block372W2) (w3 := block372W3) (w4 := block372W4)
    (s1 := block372S1) (s2 := block372S2) (s3 := block372S3) (s4 := block372S4)
    hboxes hcover block372LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block372RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block372RightChunk000 block372W1 block372W2 block372W3 block372W4 block372S1 block372S2 block372S3 block372S4

theorem block372RightChunk000ParamsCertificate_eq_true :
    block372RightChunk000ParamsCertificate = true := by
  native_decide

theorem block372_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block372RightChunk000L : ℝ) (block372RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block372S1 : ℝ))
    (hy2ne : y ≠ (block372S2 : ℝ))
    (hy3ne : y ≠ (block372S3 : ℝ))
    (hy4ne : y ≠ (block372S4 : ℝ)) :
    0 < block372V y := by
  have hcert := block372RightChunk000Certificate_eq_true
  unfold block372RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block372RightChunk000) (lo := block372RightChunk000L) (hi := block372RightChunk000R)
    (w1 := block372W1) (w2 := block372W2) (w3 := block372W3) (w4 := block372W4)
    (s1 := block372S1) (s2 := block372S2) (s3 := block372S3) (s4 := block372S4)
    hboxes hcover block372RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block372_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block372RightL : ℝ) (block372RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block372S1 : ℝ))
    (hy2ne : y ≠ (block372S2 : ℝ))
    (hy3ne : y ≠ (block372S3 : ℝ))
    (hy4ne : y ≠ (block372S4 : ℝ)) :
    0 < block372V y := by
  have hL : (block372RightChunk000L : ℝ) = (block372RightL : ℝ) := by
    norm_num [block372RightChunk000L, block372RightL]
  have hR : (block372RightChunk000R : ℝ) = (block372RightR : ℝ) := by
    norm_num [block372RightChunk000R, block372RightR]
  have hyc : y ∈ Icc (block372RightChunk000L : ℝ) (block372RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block372_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block372_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block372LeftL : ℝ) (block372LeftR : ℝ) →
    y ≠ 0 → y ≠ (block372S1 : ℝ) → y ≠ (block372S2 : ℝ) →
    y ≠ (block372S3 : ℝ) → y ≠ (block372S4 : ℝ) → 0 < block372V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block372RightL : ℝ) (block372RightR : ℝ) →
    y ≠ 0 → y ≠ (block372S1 : ℝ) → y ≠ (block372S2 : ℝ) →
    y ≠ (block372S3 : ℝ) → y ≠ (block372S4 : ℝ) → 0 < block372V y)

theorem block372_reallog_certificate_proof :
    block372_reallog_certificate := by
  exact ⟨block372_left_V_pos, block372_right_V_pos⟩

end Block372
end M1817475
end Erdos1038Lean
