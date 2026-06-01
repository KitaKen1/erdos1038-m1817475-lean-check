import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block231

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block231

open Set

def block231W1 : Rat := ((4328192971645373 : Rat) / 5000000000000000)
def block231W2 : Rat := ((8328512705504967 : Rat) / 100000000000000000)
def block231W3 : Rat := ((285262874669551 : Rat) / 1562500000000000)
def block231W4 : Rat := ((3521774264862239 : Rat) / 50000000000000000)
def block231S1 : Rat := ((18174751 : Rat) / 10000000)
def block231S2 : Rat := ((511587 : Rat) / 200000)
def block231S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block231S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block231V (y : ℝ) : ℝ :=
  ratPotential block231W1 block231W2 block231W3 block231W4 block231S1 block231S2 block231S3 block231S4 y

def block231LeftParamsCertificate : Bool :=
  allBoxesSameParams block231LeftBoxes block231W1 block231W2 block231W3 block231W4 block231S1 block231S2 block231S3 block231S4

theorem block231LeftParamsCertificate_eq_true :
    block231LeftParamsCertificate = true := by
  native_decide

theorem block231_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block231LeftL : ℝ) (block231LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block231S1 : ℝ))
    (hy2ne : y ≠ (block231S2 : ℝ))
    (hy3ne : y ≠ (block231S3 : ℝ))
    (hy4ne : y ≠ (block231S4 : ℝ)) :
    0 < block231V y := by
  have hcert := block231LeftCertificate_eq_true
  unfold block231LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block231LeftBoxes) (lo := block231LeftL) (hi := block231LeftR)
    (w1 := block231W1) (w2 := block231W2) (w3 := block231W3) (w4 := block231W4)
    (s1 := block231S1) (s2 := block231S2) (s3 := block231S3) (s4 := block231S4)
    hboxes hcover block231LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block231RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block231RightChunk000 block231W1 block231W2 block231W3 block231W4 block231S1 block231S2 block231S3 block231S4

theorem block231RightChunk000ParamsCertificate_eq_true :
    block231RightChunk000ParamsCertificate = true := by
  native_decide

theorem block231_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block231RightChunk000L : ℝ) (block231RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block231S1 : ℝ))
    (hy2ne : y ≠ (block231S2 : ℝ))
    (hy3ne : y ≠ (block231S3 : ℝ))
    (hy4ne : y ≠ (block231S4 : ℝ)) :
    0 < block231V y := by
  have hcert := block231RightChunk000Certificate_eq_true
  unfold block231RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block231RightChunk000) (lo := block231RightChunk000L) (hi := block231RightChunk000R)
    (w1 := block231W1) (w2 := block231W2) (w3 := block231W3) (w4 := block231W4)
    (s1 := block231S1) (s2 := block231S2) (s3 := block231S3) (s4 := block231S4)
    hboxes hcover block231RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block231RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block231RightChunk001 block231W1 block231W2 block231W3 block231W4 block231S1 block231S2 block231S3 block231S4

theorem block231RightChunk001ParamsCertificate_eq_true :
    block231RightChunk001ParamsCertificate = true := by
  native_decide

theorem block231_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block231RightChunk001L : ℝ) (block231RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block231S1 : ℝ))
    (hy2ne : y ≠ (block231S2 : ℝ))
    (hy3ne : y ≠ (block231S3 : ℝ))
    (hy4ne : y ≠ (block231S4 : ℝ)) :
    0 < block231V y := by
  have hcert := block231RightChunk001Certificate_eq_true
  unfold block231RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block231RightChunk001) (lo := block231RightChunk001L) (hi := block231RightChunk001R)
    (w1 := block231W1) (w2 := block231W2) (w3 := block231W3) (w4 := block231W4)
    (s1 := block231S1) (s2 := block231S2) (s3 := block231S3) (s4 := block231S4)
    hboxes hcover block231RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block231RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block231RightChunk002 block231W1 block231W2 block231W3 block231W4 block231S1 block231S2 block231S3 block231S4

theorem block231RightChunk002ParamsCertificate_eq_true :
    block231RightChunk002ParamsCertificate = true := by
  native_decide

theorem block231_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block231RightChunk002L : ℝ) (block231RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block231S1 : ℝ))
    (hy2ne : y ≠ (block231S2 : ℝ))
    (hy3ne : y ≠ (block231S3 : ℝ))
    (hy4ne : y ≠ (block231S4 : ℝ)) :
    0 < block231V y := by
  have hcert := block231RightChunk002Certificate_eq_true
  unfold block231RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block231RightChunk002) (lo := block231RightChunk002L) (hi := block231RightChunk002R)
    (w1 := block231W1) (w2 := block231W2) (w3 := block231W3) (w4 := block231W4)
    (s1 := block231S1) (s2 := block231S2) (s3 := block231S3) (s4 := block231S4)
    hboxes hcover block231RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block231_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block231RightL : ℝ) (block231RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block231S1 : ℝ))
    (hy2ne : y ≠ (block231S2 : ℝ))
    (hy3ne : y ≠ (block231S3 : ℝ))
    (hy4ne : y ≠ (block231S4 : ℝ)) :
    0 < block231V y := by
  by_cases h0 : y ≤ (block231RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block231RightChunk000L : ℝ) (block231RightChunk000R : ℝ) := by
      have hL : (block231RightChunk000L : ℝ) = (block231RightL : ℝ) := by
        norm_num [block231RightChunk000L, block231RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block231_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block231RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block231RightChunk001L : ℝ) (block231RightChunk001R : ℝ) := by
        have hprev : (block231RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block231RightChunk001L : ℝ) = (block231RightChunk000R : ℝ) := by
          norm_num [block231RightChunk001L, block231RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block231_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block231RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block231RightChunk002L : ℝ) = (block231RightChunk001R : ℝ) := by
        norm_num [block231RightChunk002L, block231RightChunk001R]
      have hR : (block231RightChunk002R : ℝ) = (block231RightR : ℝ) := by
        norm_num [block231RightChunk002R, block231RightR]
      have hyc : y ∈ Icc (block231RightChunk002L : ℝ) (block231RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block231_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block231_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block231LeftL : ℝ) (block231LeftR : ℝ) →
    y ≠ 0 → y ≠ (block231S1 : ℝ) → y ≠ (block231S2 : ℝ) →
    y ≠ (block231S3 : ℝ) → y ≠ (block231S4 : ℝ) → 0 < block231V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block231RightL : ℝ) (block231RightR : ℝ) →
    y ≠ 0 → y ≠ (block231S1 : ℝ) → y ≠ (block231S2 : ℝ) →
    y ≠ (block231S3 : ℝ) → y ≠ (block231S4 : ℝ) → 0 < block231V y)

theorem block231_reallog_certificate_proof :
    block231_reallog_certificate := by
  exact ⟨block231_left_V_pos, block231_right_V_pos⟩

end Block231
end M1817475
end Erdos1038Lean
