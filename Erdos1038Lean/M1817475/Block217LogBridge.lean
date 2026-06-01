import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block217

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block217

open Set

def block217W1 : Rat := ((4810387725241077 : Rat) / 5000000000000000)
def block217W2 : Rat := ((1699295808484407 : Rat) / 31250000000000000)
def block217W3 : Rat := ((17352486999112057 : Rat) / 100000000000000000)
def block217W4 : Rat := ((2455215249826687 : Rat) / 25000000000000000)
def block217S1 : Rat := ((18174751 : Rat) / 10000000)
def block217S2 : Rat := ((511587 : Rat) / 200000)
def block217S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block217S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block217V (y : ℝ) : ℝ :=
  ratPotential block217W1 block217W2 block217W3 block217W4 block217S1 block217S2 block217S3 block217S4 y

def block217LeftParamsCertificate : Bool :=
  allBoxesSameParams block217LeftBoxes block217W1 block217W2 block217W3 block217W4 block217S1 block217S2 block217S3 block217S4

theorem block217LeftParamsCertificate_eq_true :
    block217LeftParamsCertificate = true := by
  native_decide

theorem block217_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block217LeftL : ℝ) (block217LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block217S1 : ℝ))
    (hy2ne : y ≠ (block217S2 : ℝ))
    (hy3ne : y ≠ (block217S3 : ℝ))
    (hy4ne : y ≠ (block217S4 : ℝ)) :
    0 < block217V y := by
  have hcert := block217LeftCertificate_eq_true
  unfold block217LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block217LeftBoxes) (lo := block217LeftL) (hi := block217LeftR)
    (w1 := block217W1) (w2 := block217W2) (w3 := block217W3) (w4 := block217W4)
    (s1 := block217S1) (s2 := block217S2) (s3 := block217S3) (s4 := block217S4)
    hboxes hcover block217LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block217RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block217RightChunk000 block217W1 block217W2 block217W3 block217W4 block217S1 block217S2 block217S3 block217S4

theorem block217RightChunk000ParamsCertificate_eq_true :
    block217RightChunk000ParamsCertificate = true := by
  native_decide

theorem block217_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block217RightChunk000L : ℝ) (block217RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block217S1 : ℝ))
    (hy2ne : y ≠ (block217S2 : ℝ))
    (hy3ne : y ≠ (block217S3 : ℝ))
    (hy4ne : y ≠ (block217S4 : ℝ)) :
    0 < block217V y := by
  have hcert := block217RightChunk000Certificate_eq_true
  unfold block217RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block217RightChunk000) (lo := block217RightChunk000L) (hi := block217RightChunk000R)
    (w1 := block217W1) (w2 := block217W2) (w3 := block217W3) (w4 := block217W4)
    (s1 := block217S1) (s2 := block217S2) (s3 := block217S3) (s4 := block217S4)
    hboxes hcover block217RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block217RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block217RightChunk001 block217W1 block217W2 block217W3 block217W4 block217S1 block217S2 block217S3 block217S4

theorem block217RightChunk001ParamsCertificate_eq_true :
    block217RightChunk001ParamsCertificate = true := by
  native_decide

theorem block217_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block217RightChunk001L : ℝ) (block217RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block217S1 : ℝ))
    (hy2ne : y ≠ (block217S2 : ℝ))
    (hy3ne : y ≠ (block217S3 : ℝ))
    (hy4ne : y ≠ (block217S4 : ℝ)) :
    0 < block217V y := by
  have hcert := block217RightChunk001Certificate_eq_true
  unfold block217RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block217RightChunk001) (lo := block217RightChunk001L) (hi := block217RightChunk001R)
    (w1 := block217W1) (w2 := block217W2) (w3 := block217W3) (w4 := block217W4)
    (s1 := block217S1) (s2 := block217S2) (s3 := block217S3) (s4 := block217S4)
    hboxes hcover block217RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block217RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block217RightChunk002 block217W1 block217W2 block217W3 block217W4 block217S1 block217S2 block217S3 block217S4

theorem block217RightChunk002ParamsCertificate_eq_true :
    block217RightChunk002ParamsCertificate = true := by
  native_decide

theorem block217_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block217RightChunk002L : ℝ) (block217RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block217S1 : ℝ))
    (hy2ne : y ≠ (block217S2 : ℝ))
    (hy3ne : y ≠ (block217S3 : ℝ))
    (hy4ne : y ≠ (block217S4 : ℝ)) :
    0 < block217V y := by
  have hcert := block217RightChunk002Certificate_eq_true
  unfold block217RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block217RightChunk002) (lo := block217RightChunk002L) (hi := block217RightChunk002R)
    (w1 := block217W1) (w2 := block217W2) (w3 := block217W3) (w4 := block217W4)
    (s1 := block217S1) (s2 := block217S2) (s3 := block217S3) (s4 := block217S4)
    hboxes hcover block217RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block217_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block217RightL : ℝ) (block217RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block217S1 : ℝ))
    (hy2ne : y ≠ (block217S2 : ℝ))
    (hy3ne : y ≠ (block217S3 : ℝ))
    (hy4ne : y ≠ (block217S4 : ℝ)) :
    0 < block217V y := by
  by_cases h0 : y ≤ (block217RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block217RightChunk000L : ℝ) (block217RightChunk000R : ℝ) := by
      have hL : (block217RightChunk000L : ℝ) = (block217RightL : ℝ) := by
        norm_num [block217RightChunk000L, block217RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block217_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block217RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block217RightChunk001L : ℝ) (block217RightChunk001R : ℝ) := by
        have hprev : (block217RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block217RightChunk001L : ℝ) = (block217RightChunk000R : ℝ) := by
          norm_num [block217RightChunk001L, block217RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block217_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block217RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block217RightChunk002L : ℝ) = (block217RightChunk001R : ℝ) := by
        norm_num [block217RightChunk002L, block217RightChunk001R]
      have hR : (block217RightChunk002R : ℝ) = (block217RightR : ℝ) := by
        norm_num [block217RightChunk002R, block217RightR]
      have hyc : y ∈ Icc (block217RightChunk002L : ℝ) (block217RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block217_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block217_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block217LeftL : ℝ) (block217LeftR : ℝ) →
    y ≠ 0 → y ≠ (block217S1 : ℝ) → y ≠ (block217S2 : ℝ) →
    y ≠ (block217S3 : ℝ) → y ≠ (block217S4 : ℝ) → 0 < block217V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block217RightL : ℝ) (block217RightR : ℝ) →
    y ≠ 0 → y ≠ (block217S1 : ℝ) → y ≠ (block217S2 : ℝ) →
    y ≠ (block217S3 : ℝ) → y ≠ (block217S4 : ℝ) → 0 < block217V y)

theorem block217_reallog_certificate_proof :
    block217_reallog_certificate := by
  exact ⟨block217_left_V_pos, block217_right_V_pos⟩

end Block217
end M1817475
end Erdos1038Lean
