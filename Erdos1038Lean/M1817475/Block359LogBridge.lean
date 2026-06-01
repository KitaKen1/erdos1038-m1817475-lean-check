import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block359

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block359

open Set

def block359W1 : Rat := ((8881895183525733 : Rat) / 10000000000000000)
def block359W2 : Rat := ((9492909589441463 : Rat) / 200000000000000000)
def block359W3 : Rat := ((7580305176319327 : Rat) / 50000000000000000)
def block359W4 : Rat := ((6943560727791391 : Rat) / 50000000000000000)
def block359S1 : Rat := ((18174751 : Rat) / 10000000)
def block359S2 : Rat := ((511587 : Rat) / 200000)
def block359S3 : Rat := ((26623085553571428577 : Rat) / 10000000000000000000)
def block359S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block359V (y : ℝ) : ℝ :=
  ratPotential block359W1 block359W2 block359W3 block359W4 block359S1 block359S2 block359S3 block359S4 y

def block359LeftParamsCertificate : Bool :=
  allBoxesSameParams block359LeftBoxes block359W1 block359W2 block359W3 block359W4 block359S1 block359S2 block359S3 block359S4

theorem block359LeftParamsCertificate_eq_true :
    block359LeftParamsCertificate = true := by
  native_decide

theorem block359_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block359LeftL : ℝ) (block359LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block359S1 : ℝ))
    (hy2ne : y ≠ (block359S2 : ℝ))
    (hy3ne : y ≠ (block359S3 : ℝ))
    (hy4ne : y ≠ (block359S4 : ℝ)) :
    0 < block359V y := by
  have hcert := block359LeftCertificate_eq_true
  unfold block359LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block359LeftBoxes) (lo := block359LeftL) (hi := block359LeftR)
    (w1 := block359W1) (w2 := block359W2) (w3 := block359W3) (w4 := block359W4)
    (s1 := block359S1) (s2 := block359S2) (s3 := block359S3) (s4 := block359S4)
    hboxes hcover block359LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block359RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block359RightChunk000 block359W1 block359W2 block359W3 block359W4 block359S1 block359S2 block359S3 block359S4

theorem block359RightChunk000ParamsCertificate_eq_true :
    block359RightChunk000ParamsCertificate = true := by
  native_decide

theorem block359_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block359RightChunk000L : ℝ) (block359RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block359S1 : ℝ))
    (hy2ne : y ≠ (block359S2 : ℝ))
    (hy3ne : y ≠ (block359S3 : ℝ))
    (hy4ne : y ≠ (block359S4 : ℝ)) :
    0 < block359V y := by
  have hcert := block359RightChunk000Certificate_eq_true
  unfold block359RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block359RightChunk000) (lo := block359RightChunk000L) (hi := block359RightChunk000R)
    (w1 := block359W1) (w2 := block359W2) (w3 := block359W3) (w4 := block359W4)
    (s1 := block359S1) (s2 := block359S2) (s3 := block359S3) (s4 := block359S4)
    hboxes hcover block359RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block359_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block359RightL : ℝ) (block359RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block359S1 : ℝ))
    (hy2ne : y ≠ (block359S2 : ℝ))
    (hy3ne : y ≠ (block359S3 : ℝ))
    (hy4ne : y ≠ (block359S4 : ℝ)) :
    0 < block359V y := by
  have hL : (block359RightChunk000L : ℝ) = (block359RightL : ℝ) := by
    norm_num [block359RightChunk000L, block359RightL]
  have hR : (block359RightChunk000R : ℝ) = (block359RightR : ℝ) := by
    norm_num [block359RightChunk000R, block359RightR]
  have hyc : y ∈ Icc (block359RightChunk000L : ℝ) (block359RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block359_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block359_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block359LeftL : ℝ) (block359LeftR : ℝ) →
    y ≠ 0 → y ≠ (block359S1 : ℝ) → y ≠ (block359S2 : ℝ) →
    y ≠ (block359S3 : ℝ) → y ≠ (block359S4 : ℝ) → 0 < block359V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block359RightL : ℝ) (block359RightR : ℝ) →
    y ≠ 0 → y ≠ (block359S1 : ℝ) → y ≠ (block359S2 : ℝ) →
    y ≠ (block359S3 : ℝ) → y ≠ (block359S4 : ℝ) → 0 < block359V y)

theorem block359_reallog_certificate_proof :
    block359_reallog_certificate := by
  exact ⟨block359_left_V_pos, block359_right_V_pos⟩

end Block359
end M1817475
end Erdos1038Lean
