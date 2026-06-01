import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block212

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block212

open Set

def block212W1 : Rat := ((1930701260919609 : Rat) / 2000000000000000)
def block212W2 : Rat := ((5334666912987847 : Rat) / 100000000000000000)
def block212W3 : Rat := ((2185712142684389 : Rat) / 12500000000000000)
def block212W4 : Rat := ((9755708498371943 : Rat) / 100000000000000000)
def block212S1 : Rat := ((18174751 : Rat) / 10000000)
def block212S2 : Rat := ((511587 : Rat) / 200000)
def block212S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block212S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block212V (y : ℝ) : ℝ :=
  ratPotential block212W1 block212W2 block212W3 block212W4 block212S1 block212S2 block212S3 block212S4 y

def block212LeftParamsCertificate : Bool :=
  allBoxesSameParams block212LeftBoxes block212W1 block212W2 block212W3 block212W4 block212S1 block212S2 block212S3 block212S4

theorem block212LeftParamsCertificate_eq_true :
    block212LeftParamsCertificate = true := by
  native_decide

theorem block212_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block212LeftL : ℝ) (block212LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block212S1 : ℝ))
    (hy2ne : y ≠ (block212S2 : ℝ))
    (hy3ne : y ≠ (block212S3 : ℝ))
    (hy4ne : y ≠ (block212S4 : ℝ)) :
    0 < block212V y := by
  have hcert := block212LeftCertificate_eq_true
  unfold block212LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block212LeftBoxes) (lo := block212LeftL) (hi := block212LeftR)
    (w1 := block212W1) (w2 := block212W2) (w3 := block212W3) (w4 := block212W4)
    (s1 := block212S1) (s2 := block212S2) (s3 := block212S3) (s4 := block212S4)
    hboxes hcover block212LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block212RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block212RightChunk000 block212W1 block212W2 block212W3 block212W4 block212S1 block212S2 block212S3 block212S4

theorem block212RightChunk000ParamsCertificate_eq_true :
    block212RightChunk000ParamsCertificate = true := by
  native_decide

theorem block212_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block212RightChunk000L : ℝ) (block212RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block212S1 : ℝ))
    (hy2ne : y ≠ (block212S2 : ℝ))
    (hy3ne : y ≠ (block212S3 : ℝ))
    (hy4ne : y ≠ (block212S4 : ℝ)) :
    0 < block212V y := by
  have hcert := block212RightChunk000Certificate_eq_true
  unfold block212RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block212RightChunk000) (lo := block212RightChunk000L) (hi := block212RightChunk000R)
    (w1 := block212W1) (w2 := block212W2) (w3 := block212W3) (w4 := block212W4)
    (s1 := block212S1) (s2 := block212S2) (s3 := block212S3) (s4 := block212S4)
    hboxes hcover block212RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block212RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block212RightChunk001 block212W1 block212W2 block212W3 block212W4 block212S1 block212S2 block212S3 block212S4

theorem block212RightChunk001ParamsCertificate_eq_true :
    block212RightChunk001ParamsCertificate = true := by
  native_decide

theorem block212_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block212RightChunk001L : ℝ) (block212RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block212S1 : ℝ))
    (hy2ne : y ≠ (block212S2 : ℝ))
    (hy3ne : y ≠ (block212S3 : ℝ))
    (hy4ne : y ≠ (block212S4 : ℝ)) :
    0 < block212V y := by
  have hcert := block212RightChunk001Certificate_eq_true
  unfold block212RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block212RightChunk001) (lo := block212RightChunk001L) (hi := block212RightChunk001R)
    (w1 := block212W1) (w2 := block212W2) (w3 := block212W3) (w4 := block212W4)
    (s1 := block212S1) (s2 := block212S2) (s3 := block212S3) (s4 := block212S4)
    hboxes hcover block212RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block212RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block212RightChunk002 block212W1 block212W2 block212W3 block212W4 block212S1 block212S2 block212S3 block212S4

theorem block212RightChunk002ParamsCertificate_eq_true :
    block212RightChunk002ParamsCertificate = true := by
  native_decide

theorem block212_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block212RightChunk002L : ℝ) (block212RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block212S1 : ℝ))
    (hy2ne : y ≠ (block212S2 : ℝ))
    (hy3ne : y ≠ (block212S3 : ℝ))
    (hy4ne : y ≠ (block212S4 : ℝ)) :
    0 < block212V y := by
  have hcert := block212RightChunk002Certificate_eq_true
  unfold block212RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block212RightChunk002) (lo := block212RightChunk002L) (hi := block212RightChunk002R)
    (w1 := block212W1) (w2 := block212W2) (w3 := block212W3) (w4 := block212W4)
    (s1 := block212S1) (s2 := block212S2) (s3 := block212S3) (s4 := block212S4)
    hboxes hcover block212RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block212RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block212RightChunk003 block212W1 block212W2 block212W3 block212W4 block212S1 block212S2 block212S3 block212S4

theorem block212RightChunk003ParamsCertificate_eq_true :
    block212RightChunk003ParamsCertificate = true := by
  native_decide

theorem block212_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block212RightChunk003L : ℝ) (block212RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block212S1 : ℝ))
    (hy2ne : y ≠ (block212S2 : ℝ))
    (hy3ne : y ≠ (block212S3 : ℝ))
    (hy4ne : y ≠ (block212S4 : ℝ)) :
    0 < block212V y := by
  have hcert := block212RightChunk003Certificate_eq_true
  unfold block212RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block212RightChunk003) (lo := block212RightChunk003L) (hi := block212RightChunk003R)
    (w1 := block212W1) (w2 := block212W2) (w3 := block212W3) (w4 := block212W4)
    (s1 := block212S1) (s2 := block212S2) (s3 := block212S3) (s4 := block212S4)
    hboxes hcover block212RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block212_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block212RightL : ℝ) (block212RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block212S1 : ℝ))
    (hy2ne : y ≠ (block212S2 : ℝ))
    (hy3ne : y ≠ (block212S3 : ℝ))
    (hy4ne : y ≠ (block212S4 : ℝ)) :
    0 < block212V y := by
  by_cases h0 : y ≤ (block212RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block212RightChunk000L : ℝ) (block212RightChunk000R : ℝ) := by
      have hL : (block212RightChunk000L : ℝ) = (block212RightL : ℝ) := by
        norm_num [block212RightChunk000L, block212RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block212_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block212RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block212RightChunk001L : ℝ) (block212RightChunk001R : ℝ) := by
        have hprev : (block212RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block212RightChunk001L : ℝ) = (block212RightChunk000R : ℝ) := by
          norm_num [block212RightChunk001L, block212RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block212_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block212RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block212RightChunk002L : ℝ) (block212RightChunk002R : ℝ) := by
          have hprev : (block212RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block212RightChunk002L : ℝ) = (block212RightChunk001R : ℝ) := by
            norm_num [block212RightChunk002L, block212RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block212_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block212RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block212RightChunk003L : ℝ) = (block212RightChunk002R : ℝ) := by
          norm_num [block212RightChunk003L, block212RightChunk002R]
        have hR : (block212RightChunk003R : ℝ) = (block212RightR : ℝ) := by
          norm_num [block212RightChunk003R, block212RightR]
        have hyc : y ∈ Icc (block212RightChunk003L : ℝ) (block212RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block212_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block212_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block212LeftL : ℝ) (block212LeftR : ℝ) →
    y ≠ 0 → y ≠ (block212S1 : ℝ) → y ≠ (block212S2 : ℝ) →
    y ≠ (block212S3 : ℝ) → y ≠ (block212S4 : ℝ) → 0 < block212V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block212RightL : ℝ) (block212RightR : ℝ) →
    y ≠ 0 → y ≠ (block212S1 : ℝ) → y ≠ (block212S2 : ℝ) →
    y ≠ (block212S3 : ℝ) → y ≠ (block212S4 : ℝ) → 0 < block212V y)

theorem block212_reallog_certificate_proof :
    block212_reallog_certificate := by
  exact ⟨block212_left_V_pos, block212_right_V_pos⟩

end Block212
end M1817475
end Erdos1038Lean
