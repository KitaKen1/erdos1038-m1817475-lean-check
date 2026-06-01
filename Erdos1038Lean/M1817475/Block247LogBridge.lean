import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block247

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block247

open Set

def block247W1 : Rat := ((4279287398989093 : Rat) / 5000000000000000)
def block247W2 : Rat := ((346637981114443 : Rat) / 4000000000000000)
def block247W3 : Rat := ((2255817644811027 : Rat) / 50000000000000000)
def block247W4 : Rat := ((4096442459848833 : Rat) / 20000000000000000)
def block247S1 : Rat := ((18174751 : Rat) / 10000000)
def block247S2 : Rat := ((511587 : Rat) / 200000)
def block247S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block247S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block247V (y : ℝ) : ℝ :=
  ratPotential block247W1 block247W2 block247W3 block247W4 block247S1 block247S2 block247S3 block247S4 y

def block247LeftParamsCertificate : Bool :=
  allBoxesSameParams block247LeftBoxes block247W1 block247W2 block247W3 block247W4 block247S1 block247S2 block247S3 block247S4

theorem block247LeftParamsCertificate_eq_true :
    block247LeftParamsCertificate = true := by
  native_decide

theorem block247_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block247LeftL : ℝ) (block247LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block247S1 : ℝ))
    (hy2ne : y ≠ (block247S2 : ℝ))
    (hy3ne : y ≠ (block247S3 : ℝ))
    (hy4ne : y ≠ (block247S4 : ℝ)) :
    0 < block247V y := by
  have hcert := block247LeftCertificate_eq_true
  unfold block247LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block247LeftBoxes) (lo := block247LeftL) (hi := block247LeftR)
    (w1 := block247W1) (w2 := block247W2) (w3 := block247W3) (w4 := block247W4)
    (s1 := block247S1) (s2 := block247S2) (s3 := block247S3) (s4 := block247S4)
    hboxes hcover block247LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block247RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block247RightChunk000 block247W1 block247W2 block247W3 block247W4 block247S1 block247S2 block247S3 block247S4

theorem block247RightChunk000ParamsCertificate_eq_true :
    block247RightChunk000ParamsCertificate = true := by
  native_decide

theorem block247_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block247RightChunk000L : ℝ) (block247RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block247S1 : ℝ))
    (hy2ne : y ≠ (block247S2 : ℝ))
    (hy3ne : y ≠ (block247S3 : ℝ))
    (hy4ne : y ≠ (block247S4 : ℝ)) :
    0 < block247V y := by
  have hcert := block247RightChunk000Certificate_eq_true
  unfold block247RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block247RightChunk000) (lo := block247RightChunk000L) (hi := block247RightChunk000R)
    (w1 := block247W1) (w2 := block247W2) (w3 := block247W3) (w4 := block247W4)
    (s1 := block247S1) (s2 := block247S2) (s3 := block247S3) (s4 := block247S4)
    hboxes hcover block247RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block247RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block247RightChunk001 block247W1 block247W2 block247W3 block247W4 block247S1 block247S2 block247S3 block247S4

theorem block247RightChunk001ParamsCertificate_eq_true :
    block247RightChunk001ParamsCertificate = true := by
  native_decide

theorem block247_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block247RightChunk001L : ℝ) (block247RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block247S1 : ℝ))
    (hy2ne : y ≠ (block247S2 : ℝ))
    (hy3ne : y ≠ (block247S3 : ℝ))
    (hy4ne : y ≠ (block247S4 : ℝ)) :
    0 < block247V y := by
  have hcert := block247RightChunk001Certificate_eq_true
  unfold block247RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block247RightChunk001) (lo := block247RightChunk001L) (hi := block247RightChunk001R)
    (w1 := block247W1) (w2 := block247W2) (w3 := block247W3) (w4 := block247W4)
    (s1 := block247S1) (s2 := block247S2) (s3 := block247S3) (s4 := block247S4)
    hboxes hcover block247RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block247_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block247RightL : ℝ) (block247RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block247S1 : ℝ))
    (hy2ne : y ≠ (block247S2 : ℝ))
    (hy3ne : y ≠ (block247S3 : ℝ))
    (hy4ne : y ≠ (block247S4 : ℝ)) :
    0 < block247V y := by
  by_cases h0 : y ≤ (block247RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block247RightChunk000L : ℝ) (block247RightChunk000R : ℝ) := by
      have hL : (block247RightChunk000L : ℝ) = (block247RightL : ℝ) := by
        norm_num [block247RightChunk000L, block247RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block247_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block247RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block247RightChunk001L : ℝ) = (block247RightChunk000R : ℝ) := by
      norm_num [block247RightChunk001L, block247RightChunk000R]
    have hR : (block247RightChunk001R : ℝ) = (block247RightR : ℝ) := by
      norm_num [block247RightChunk001R, block247RightR]
    have hyc : y ∈ Icc (block247RightChunk001L : ℝ) (block247RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block247_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block247_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block247LeftL : ℝ) (block247LeftR : ℝ) →
    y ≠ 0 → y ≠ (block247S1 : ℝ) → y ≠ (block247S2 : ℝ) →
    y ≠ (block247S3 : ℝ) → y ≠ (block247S4 : ℝ) → 0 < block247V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block247RightL : ℝ) (block247RightR : ℝ) →
    y ≠ 0 → y ≠ (block247S1 : ℝ) → y ≠ (block247S2 : ℝ) →
    y ≠ (block247S3 : ℝ) → y ≠ (block247S4 : ℝ) → 0 < block247V y)

theorem block247_reallog_certificate_proof :
    block247_reallog_certificate := by
  exact ⟨block247_left_V_pos, block247_right_V_pos⟩

end Block247
end M1817475
end Erdos1038Lean
