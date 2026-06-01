import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block213

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block213

open Set

def block213W1 : Rat := ((482212672954589 : Rat) / 500000000000000)
def block213W2 : Rat := ((20950074456229 : Rat) / 390625000000000)
def block213W3 : Rat := ((27263205109411 : Rat) / 156250000000000)
def block213W4 : Rat := ((4886852171814237 : Rat) / 50000000000000000)
def block213S1 : Rat := ((18174751 : Rat) / 10000000)
def block213S2 : Rat := ((511587 : Rat) / 200000)
def block213S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block213S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block213V (y : ℝ) : ℝ :=
  ratPotential block213W1 block213W2 block213W3 block213W4 block213S1 block213S2 block213S3 block213S4 y

def block213LeftParamsCertificate : Bool :=
  allBoxesSameParams block213LeftBoxes block213W1 block213W2 block213W3 block213W4 block213S1 block213S2 block213S3 block213S4

theorem block213LeftParamsCertificate_eq_true :
    block213LeftParamsCertificate = true := by
  native_decide

theorem block213_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block213LeftL : ℝ) (block213LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block213S1 : ℝ))
    (hy2ne : y ≠ (block213S2 : ℝ))
    (hy3ne : y ≠ (block213S3 : ℝ))
    (hy4ne : y ≠ (block213S4 : ℝ)) :
    0 < block213V y := by
  have hcert := block213LeftCertificate_eq_true
  unfold block213LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block213LeftBoxes) (lo := block213LeftL) (hi := block213LeftR)
    (w1 := block213W1) (w2 := block213W2) (w3 := block213W3) (w4 := block213W4)
    (s1 := block213S1) (s2 := block213S2) (s3 := block213S3) (s4 := block213S4)
    hboxes hcover block213LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block213RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block213RightChunk000 block213W1 block213W2 block213W3 block213W4 block213S1 block213S2 block213S3 block213S4

theorem block213RightChunk000ParamsCertificate_eq_true :
    block213RightChunk000ParamsCertificate = true := by
  native_decide

theorem block213_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block213RightChunk000L : ℝ) (block213RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block213S1 : ℝ))
    (hy2ne : y ≠ (block213S2 : ℝ))
    (hy3ne : y ≠ (block213S3 : ℝ))
    (hy4ne : y ≠ (block213S4 : ℝ)) :
    0 < block213V y := by
  have hcert := block213RightChunk000Certificate_eq_true
  unfold block213RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block213RightChunk000) (lo := block213RightChunk000L) (hi := block213RightChunk000R)
    (w1 := block213W1) (w2 := block213W2) (w3 := block213W3) (w4 := block213W4)
    (s1 := block213S1) (s2 := block213S2) (s3 := block213S3) (s4 := block213S4)
    hboxes hcover block213RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block213RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block213RightChunk001 block213W1 block213W2 block213W3 block213W4 block213S1 block213S2 block213S3 block213S4

theorem block213RightChunk001ParamsCertificate_eq_true :
    block213RightChunk001ParamsCertificate = true := by
  native_decide

theorem block213_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block213RightChunk001L : ℝ) (block213RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block213S1 : ℝ))
    (hy2ne : y ≠ (block213S2 : ℝ))
    (hy3ne : y ≠ (block213S3 : ℝ))
    (hy4ne : y ≠ (block213S4 : ℝ)) :
    0 < block213V y := by
  have hcert := block213RightChunk001Certificate_eq_true
  unfold block213RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block213RightChunk001) (lo := block213RightChunk001L) (hi := block213RightChunk001R)
    (w1 := block213W1) (w2 := block213W2) (w3 := block213W3) (w4 := block213W4)
    (s1 := block213S1) (s2 := block213S2) (s3 := block213S3) (s4 := block213S4)
    hboxes hcover block213RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block213RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block213RightChunk002 block213W1 block213W2 block213W3 block213W4 block213S1 block213S2 block213S3 block213S4

theorem block213RightChunk002ParamsCertificate_eq_true :
    block213RightChunk002ParamsCertificate = true := by
  native_decide

theorem block213_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block213RightChunk002L : ℝ) (block213RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block213S1 : ℝ))
    (hy2ne : y ≠ (block213S2 : ℝ))
    (hy3ne : y ≠ (block213S3 : ℝ))
    (hy4ne : y ≠ (block213S4 : ℝ)) :
    0 < block213V y := by
  have hcert := block213RightChunk002Certificate_eq_true
  unfold block213RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block213RightChunk002) (lo := block213RightChunk002L) (hi := block213RightChunk002R)
    (w1 := block213W1) (w2 := block213W2) (w3 := block213W3) (w4 := block213W4)
    (s1 := block213S1) (s2 := block213S2) (s3 := block213S3) (s4 := block213S4)
    hboxes hcover block213RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block213RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block213RightChunk003 block213W1 block213W2 block213W3 block213W4 block213S1 block213S2 block213S3 block213S4

theorem block213RightChunk003ParamsCertificate_eq_true :
    block213RightChunk003ParamsCertificate = true := by
  native_decide

theorem block213_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block213RightChunk003L : ℝ) (block213RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block213S1 : ℝ))
    (hy2ne : y ≠ (block213S2 : ℝ))
    (hy3ne : y ≠ (block213S3 : ℝ))
    (hy4ne : y ≠ (block213S4 : ℝ)) :
    0 < block213V y := by
  have hcert := block213RightChunk003Certificate_eq_true
  unfold block213RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block213RightChunk003) (lo := block213RightChunk003L) (hi := block213RightChunk003R)
    (w1 := block213W1) (w2 := block213W2) (w3 := block213W3) (w4 := block213W4)
    (s1 := block213S1) (s2 := block213S2) (s3 := block213S3) (s4 := block213S4)
    hboxes hcover block213RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block213_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block213RightL : ℝ) (block213RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block213S1 : ℝ))
    (hy2ne : y ≠ (block213S2 : ℝ))
    (hy3ne : y ≠ (block213S3 : ℝ))
    (hy4ne : y ≠ (block213S4 : ℝ)) :
    0 < block213V y := by
  by_cases h0 : y ≤ (block213RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block213RightChunk000L : ℝ) (block213RightChunk000R : ℝ) := by
      have hL : (block213RightChunk000L : ℝ) = (block213RightL : ℝ) := by
        norm_num [block213RightChunk000L, block213RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block213_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block213RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block213RightChunk001L : ℝ) (block213RightChunk001R : ℝ) := by
        have hprev : (block213RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block213RightChunk001L : ℝ) = (block213RightChunk000R : ℝ) := by
          norm_num [block213RightChunk001L, block213RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block213_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block213RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block213RightChunk002L : ℝ) (block213RightChunk002R : ℝ) := by
          have hprev : (block213RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block213RightChunk002L : ℝ) = (block213RightChunk001R : ℝ) := by
            norm_num [block213RightChunk002L, block213RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block213_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block213RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block213RightChunk003L : ℝ) = (block213RightChunk002R : ℝ) := by
          norm_num [block213RightChunk003L, block213RightChunk002R]
        have hR : (block213RightChunk003R : ℝ) = (block213RightR : ℝ) := by
          norm_num [block213RightChunk003R, block213RightR]
        have hyc : y ∈ Icc (block213RightChunk003L : ℝ) (block213RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block213_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block213_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block213LeftL : ℝ) (block213LeftR : ℝ) →
    y ≠ 0 → y ≠ (block213S1 : ℝ) → y ≠ (block213S2 : ℝ) →
    y ≠ (block213S3 : ℝ) → y ≠ (block213S4 : ℝ) → 0 < block213V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block213RightL : ℝ) (block213RightR : ℝ) →
    y ≠ 0 → y ≠ (block213S1 : ℝ) → y ≠ (block213S2 : ℝ) →
    y ≠ (block213S3 : ℝ) → y ≠ (block213S4 : ℝ) → 0 < block213V y)

theorem block213_reallog_certificate_proof :
    block213_reallog_certificate := by
  exact ⟨block213_left_V_pos, block213_right_V_pos⟩

end Block213
end M1817475
end Erdos1038Lean
