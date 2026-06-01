import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block497

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block497

open Set

def block497W1 : Rat := ((1173457092222079 : Rat) / 2500000000000000)
def block497W2 : Rat := (0 : Rat)
def block497W3 : Rat := ((2046394956655957 : Rat) / 5000000000000000)
def block497W4 : Rat := ((23351628030011697 : Rat) / 1000000000000000000)
def block497S1 : Rat := ((18174751 : Rat) / 10000000)
def block497S2 : Rat := ((511587 : Rat) / 200000)
def block497S3 : Rat := ((130417650982142857289 : Rat) / 50000000000000000000)
def block497S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block497V (y : ℝ) : ℝ :=
  ratPotential block497W1 block497W2 block497W3 block497W4 block497S1 block497S2 block497S3 block497S4 y

def block497LeftParamsCertificate : Bool :=
  allBoxesSameParams block497LeftBoxes block497W1 block497W2 block497W3 block497W4 block497S1 block497S2 block497S3 block497S4

theorem block497LeftParamsCertificate_eq_true :
    block497LeftParamsCertificate = true := by
  native_decide

theorem block497_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block497LeftL : ℝ) (block497LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block497S1 : ℝ))
    (hy2ne : y ≠ (block497S2 : ℝ))
    (hy3ne : y ≠ (block497S3 : ℝ))
    (hy4ne : y ≠ (block497S4 : ℝ)) :
    0 < block497V y := by
  have hcert := block497LeftCertificate_eq_true
  unfold block497LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block497LeftBoxes) (lo := block497LeftL) (hi := block497LeftR)
    (w1 := block497W1) (w2 := block497W2) (w3 := block497W3) (w4 := block497W4)
    (s1 := block497S1) (s2 := block497S2) (s3 := block497S3) (s4 := block497S4)
    hboxes hcover block497LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block497RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block497RightChunk000 block497W1 block497W2 block497W3 block497W4 block497S1 block497S2 block497S3 block497S4

theorem block497RightChunk000ParamsCertificate_eq_true :
    block497RightChunk000ParamsCertificate = true := by
  native_decide

theorem block497_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block497RightChunk000L : ℝ) (block497RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block497S1 : ℝ))
    (hy2ne : y ≠ (block497S2 : ℝ))
    (hy3ne : y ≠ (block497S3 : ℝ))
    (hy4ne : y ≠ (block497S4 : ℝ)) :
    0 < block497V y := by
  have hcert := block497RightChunk000Certificate_eq_true
  unfold block497RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block497RightChunk000) (lo := block497RightChunk000L) (hi := block497RightChunk000R)
    (w1 := block497W1) (w2 := block497W2) (w3 := block497W3) (w4 := block497W4)
    (s1 := block497S1) (s2 := block497S2) (s3 := block497S3) (s4 := block497S4)
    hboxes hcover block497RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block497_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block497RightL : ℝ) (block497RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block497S1 : ℝ))
    (hy2ne : y ≠ (block497S2 : ℝ))
    (hy3ne : y ≠ (block497S3 : ℝ))
    (hy4ne : y ≠ (block497S4 : ℝ)) :
    0 < block497V y := by
  have hL : (block497RightChunk000L : ℝ) = (block497RightL : ℝ) := by
    norm_num [block497RightChunk000L, block497RightL]
  have hR : (block497RightChunk000R : ℝ) = (block497RightR : ℝ) := by
    norm_num [block497RightChunk000R, block497RightR]
  have hyc : y ∈ Icc (block497RightChunk000L : ℝ) (block497RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block497_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block497_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block497LeftL : ℝ) (block497LeftR : ℝ) →
    y ≠ 0 → y ≠ (block497S1 : ℝ) → y ≠ (block497S2 : ℝ) →
    y ≠ (block497S3 : ℝ) → y ≠ (block497S4 : ℝ) → 0 < block497V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block497RightL : ℝ) (block497RightR : ℝ) →
    y ≠ 0 → y ≠ (block497S1 : ℝ) → y ≠ (block497S2 : ℝ) →
    y ≠ (block497S3 : ℝ) → y ≠ (block497S4 : ℝ) → 0 < block497V y)

theorem block497_reallog_certificate_proof :
    block497_reallog_certificate := by
  exact ⟨block497_left_V_pos, block497_right_V_pos⟩

end Block497
end M1817475
end Erdos1038Lean
