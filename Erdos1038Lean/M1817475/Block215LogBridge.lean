import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block215

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block215

open Set

def block215W1 : Rat := ((9633658547788553 : Rat) / 10000000000000000)
def block215W2 : Rat := ((5397047069899239 : Rat) / 100000000000000000)
def block215W3 : Rat := ((108781171483451 : Rat) / 625000000000000)
def block215W4 : Rat := ((9795150171451919 : Rat) / 100000000000000000)
def block215S1 : Rat := ((18174751 : Rat) / 10000000)
def block215S2 : Rat := ((511587 : Rat) / 200000)
def block215S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block215S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block215V (y : ℝ) : ℝ :=
  ratPotential block215W1 block215W2 block215W3 block215W4 block215S1 block215S2 block215S3 block215S4 y

def block215LeftParamsCertificate : Bool :=
  allBoxesSameParams block215LeftBoxes block215W1 block215W2 block215W3 block215W4 block215S1 block215S2 block215S3 block215S4

theorem block215LeftParamsCertificate_eq_true :
    block215LeftParamsCertificate = true := by
  native_decide

theorem block215_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block215LeftL : ℝ) (block215LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block215S1 : ℝ))
    (hy2ne : y ≠ (block215S2 : ℝ))
    (hy3ne : y ≠ (block215S3 : ℝ))
    (hy4ne : y ≠ (block215S4 : ℝ)) :
    0 < block215V y := by
  have hcert := block215LeftCertificate_eq_true
  unfold block215LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block215LeftBoxes) (lo := block215LeftL) (hi := block215LeftR)
    (w1 := block215W1) (w2 := block215W2) (w3 := block215W3) (w4 := block215W4)
    (s1 := block215S1) (s2 := block215S2) (s3 := block215S3) (s4 := block215S4)
    hboxes hcover block215LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block215RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block215RightChunk000 block215W1 block215W2 block215W3 block215W4 block215S1 block215S2 block215S3 block215S4

theorem block215RightChunk000ParamsCertificate_eq_true :
    block215RightChunk000ParamsCertificate = true := by
  native_decide

theorem block215_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block215RightChunk000L : ℝ) (block215RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block215S1 : ℝ))
    (hy2ne : y ≠ (block215S2 : ℝ))
    (hy3ne : y ≠ (block215S3 : ℝ))
    (hy4ne : y ≠ (block215S4 : ℝ)) :
    0 < block215V y := by
  have hcert := block215RightChunk000Certificate_eq_true
  unfold block215RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block215RightChunk000) (lo := block215RightChunk000L) (hi := block215RightChunk000R)
    (w1 := block215W1) (w2 := block215W2) (w3 := block215W3) (w4 := block215W4)
    (s1 := block215S1) (s2 := block215S2) (s3 := block215S3) (s4 := block215S4)
    hboxes hcover block215RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block215RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block215RightChunk001 block215W1 block215W2 block215W3 block215W4 block215S1 block215S2 block215S3 block215S4

theorem block215RightChunk001ParamsCertificate_eq_true :
    block215RightChunk001ParamsCertificate = true := by
  native_decide

theorem block215_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block215RightChunk001L : ℝ) (block215RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block215S1 : ℝ))
    (hy2ne : y ≠ (block215S2 : ℝ))
    (hy3ne : y ≠ (block215S3 : ℝ))
    (hy4ne : y ≠ (block215S4 : ℝ)) :
    0 < block215V y := by
  have hcert := block215RightChunk001Certificate_eq_true
  unfold block215RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block215RightChunk001) (lo := block215RightChunk001L) (hi := block215RightChunk001R)
    (w1 := block215W1) (w2 := block215W2) (w3 := block215W3) (w4 := block215W4)
    (s1 := block215S1) (s2 := block215S2) (s3 := block215S3) (s4 := block215S4)
    hboxes hcover block215RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block215RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block215RightChunk002 block215W1 block215W2 block215W3 block215W4 block215S1 block215S2 block215S3 block215S4

theorem block215RightChunk002ParamsCertificate_eq_true :
    block215RightChunk002ParamsCertificate = true := by
  native_decide

theorem block215_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block215RightChunk002L : ℝ) (block215RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block215S1 : ℝ))
    (hy2ne : y ≠ (block215S2 : ℝ))
    (hy3ne : y ≠ (block215S3 : ℝ))
    (hy4ne : y ≠ (block215S4 : ℝ)) :
    0 < block215V y := by
  have hcert := block215RightChunk002Certificate_eq_true
  unfold block215RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block215RightChunk002) (lo := block215RightChunk002L) (hi := block215RightChunk002R)
    (w1 := block215W1) (w2 := block215W2) (w3 := block215W3) (w4 := block215W4)
    (s1 := block215S1) (s2 := block215S2) (s3 := block215S3) (s4 := block215S4)
    hboxes hcover block215RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block215RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block215RightChunk003 block215W1 block215W2 block215W3 block215W4 block215S1 block215S2 block215S3 block215S4

theorem block215RightChunk003ParamsCertificate_eq_true :
    block215RightChunk003ParamsCertificate = true := by
  native_decide

theorem block215_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block215RightChunk003L : ℝ) (block215RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block215S1 : ℝ))
    (hy2ne : y ≠ (block215S2 : ℝ))
    (hy3ne : y ≠ (block215S3 : ℝ))
    (hy4ne : y ≠ (block215S4 : ℝ)) :
    0 < block215V y := by
  have hcert := block215RightChunk003Certificate_eq_true
  unfold block215RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block215RightChunk003) (lo := block215RightChunk003L) (hi := block215RightChunk003R)
    (w1 := block215W1) (w2 := block215W2) (w3 := block215W3) (w4 := block215W4)
    (s1 := block215S1) (s2 := block215S2) (s3 := block215S3) (s4 := block215S4)
    hboxes hcover block215RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block215_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block215RightL : ℝ) (block215RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block215S1 : ℝ))
    (hy2ne : y ≠ (block215S2 : ℝ))
    (hy3ne : y ≠ (block215S3 : ℝ))
    (hy4ne : y ≠ (block215S4 : ℝ)) :
    0 < block215V y := by
  by_cases h0 : y ≤ (block215RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block215RightChunk000L : ℝ) (block215RightChunk000R : ℝ) := by
      have hL : (block215RightChunk000L : ℝ) = (block215RightL : ℝ) := by
        norm_num [block215RightChunk000L, block215RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block215_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block215RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block215RightChunk001L : ℝ) (block215RightChunk001R : ℝ) := by
        have hprev : (block215RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block215RightChunk001L : ℝ) = (block215RightChunk000R : ℝ) := by
          norm_num [block215RightChunk001L, block215RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block215_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block215RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block215RightChunk002L : ℝ) (block215RightChunk002R : ℝ) := by
          have hprev : (block215RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block215RightChunk002L : ℝ) = (block215RightChunk001R : ℝ) := by
            norm_num [block215RightChunk002L, block215RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block215_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block215RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block215RightChunk003L : ℝ) = (block215RightChunk002R : ℝ) := by
          norm_num [block215RightChunk003L, block215RightChunk002R]
        have hR : (block215RightChunk003R : ℝ) = (block215RightR : ℝ) := by
          norm_num [block215RightChunk003R, block215RightR]
        have hyc : y ∈ Icc (block215RightChunk003L : ℝ) (block215RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block215_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block215_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block215LeftL : ℝ) (block215LeftR : ℝ) →
    y ≠ 0 → y ≠ (block215S1 : ℝ) → y ≠ (block215S2 : ℝ) →
    y ≠ (block215S3 : ℝ) → y ≠ (block215S4 : ℝ) → 0 < block215V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block215RightL : ℝ) (block215RightR : ℝ) →
    y ≠ 0 → y ≠ (block215S1 : ℝ) → y ≠ (block215S2 : ℝ) →
    y ≠ (block215S3 : ℝ) → y ≠ (block215S4 : ℝ) → 0 < block215V y)

theorem block215_reallog_certificate_proof :
    block215_reallog_certificate := by
  exact ⟨block215_left_V_pos, block215_right_V_pos⟩

end Block215
end M1817475
end Erdos1038Lean
