import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block207

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block207

open Set

def block207W1 : Rat := ((2421271274506073 : Rat) / 2500000000000000)
def block207W2 : Rat := ((163615099878489 : Rat) / 3125000000000000)
def block207W3 : Rat := ((352281569465297 : Rat) / 2000000000000000)
def block207W4 : Rat := ((9692973867198733 : Rat) / 100000000000000000)
def block207S1 : Rat := ((18174751 : Rat) / 10000000)
def block207S2 : Rat := ((511587 : Rat) / 200000)
def block207S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block207S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block207V (y : ℝ) : ℝ :=
  ratPotential block207W1 block207W2 block207W3 block207W4 block207S1 block207S2 block207S3 block207S4 y

def block207LeftParamsCertificate : Bool :=
  allBoxesSameParams block207LeftBoxes block207W1 block207W2 block207W3 block207W4 block207S1 block207S2 block207S3 block207S4

theorem block207LeftParamsCertificate_eq_true :
    block207LeftParamsCertificate = true := by
  native_decide

theorem block207_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block207LeftL : ℝ) (block207LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block207S1 : ℝ))
    (hy2ne : y ≠ (block207S2 : ℝ))
    (hy3ne : y ≠ (block207S3 : ℝ))
    (hy4ne : y ≠ (block207S4 : ℝ)) :
    0 < block207V y := by
  have hcert := block207LeftCertificate_eq_true
  unfold block207LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block207LeftBoxes) (lo := block207LeftL) (hi := block207LeftR)
    (w1 := block207W1) (w2 := block207W2) (w3 := block207W3) (w4 := block207W4)
    (s1 := block207S1) (s2 := block207S2) (s3 := block207S3) (s4 := block207S4)
    hboxes hcover block207LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block207RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block207RightChunk000 block207W1 block207W2 block207W3 block207W4 block207S1 block207S2 block207S3 block207S4

theorem block207RightChunk000ParamsCertificate_eq_true :
    block207RightChunk000ParamsCertificate = true := by
  native_decide

theorem block207_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block207RightChunk000L : ℝ) (block207RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block207S1 : ℝ))
    (hy2ne : y ≠ (block207S2 : ℝ))
    (hy3ne : y ≠ (block207S3 : ℝ))
    (hy4ne : y ≠ (block207S4 : ℝ)) :
    0 < block207V y := by
  have hcert := block207RightChunk000Certificate_eq_true
  unfold block207RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block207RightChunk000) (lo := block207RightChunk000L) (hi := block207RightChunk000R)
    (w1 := block207W1) (w2 := block207W2) (w3 := block207W3) (w4 := block207W4)
    (s1 := block207S1) (s2 := block207S2) (s3 := block207S3) (s4 := block207S4)
    hboxes hcover block207RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block207RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block207RightChunk001 block207W1 block207W2 block207W3 block207W4 block207S1 block207S2 block207S3 block207S4

theorem block207RightChunk001ParamsCertificate_eq_true :
    block207RightChunk001ParamsCertificate = true := by
  native_decide

theorem block207_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block207RightChunk001L : ℝ) (block207RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block207S1 : ℝ))
    (hy2ne : y ≠ (block207S2 : ℝ))
    (hy3ne : y ≠ (block207S3 : ℝ))
    (hy4ne : y ≠ (block207S4 : ℝ)) :
    0 < block207V y := by
  have hcert := block207RightChunk001Certificate_eq_true
  unfold block207RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block207RightChunk001) (lo := block207RightChunk001L) (hi := block207RightChunk001R)
    (w1 := block207W1) (w2 := block207W2) (w3 := block207W3) (w4 := block207W4)
    (s1 := block207S1) (s2 := block207S2) (s3 := block207S3) (s4 := block207S4)
    hboxes hcover block207RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block207RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block207RightChunk002 block207W1 block207W2 block207W3 block207W4 block207S1 block207S2 block207S3 block207S4

theorem block207RightChunk002ParamsCertificate_eq_true :
    block207RightChunk002ParamsCertificate = true := by
  native_decide

theorem block207_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block207RightChunk002L : ℝ) (block207RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block207S1 : ℝ))
    (hy2ne : y ≠ (block207S2 : ℝ))
    (hy3ne : y ≠ (block207S3 : ℝ))
    (hy4ne : y ≠ (block207S4 : ℝ)) :
    0 < block207V y := by
  have hcert := block207RightChunk002Certificate_eq_true
  unfold block207RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block207RightChunk002) (lo := block207RightChunk002L) (hi := block207RightChunk002R)
    (w1 := block207W1) (w2 := block207W2) (w3 := block207W3) (w4 := block207W4)
    (s1 := block207S1) (s2 := block207S2) (s3 := block207S3) (s4 := block207S4)
    hboxes hcover block207RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block207RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block207RightChunk003 block207W1 block207W2 block207W3 block207W4 block207S1 block207S2 block207S3 block207S4

theorem block207RightChunk003ParamsCertificate_eq_true :
    block207RightChunk003ParamsCertificate = true := by
  native_decide

theorem block207_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block207RightChunk003L : ℝ) (block207RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block207S1 : ℝ))
    (hy2ne : y ≠ (block207S2 : ℝ))
    (hy3ne : y ≠ (block207S3 : ℝ))
    (hy4ne : y ≠ (block207S4 : ℝ)) :
    0 < block207V y := by
  have hcert := block207RightChunk003Certificate_eq_true
  unfold block207RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block207RightChunk003) (lo := block207RightChunk003L) (hi := block207RightChunk003R)
    (w1 := block207W1) (w2 := block207W2) (w3 := block207W3) (w4 := block207W4)
    (s1 := block207S1) (s2 := block207S2) (s3 := block207S3) (s4 := block207S4)
    hboxes hcover block207RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block207_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block207RightL : ℝ) (block207RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block207S1 : ℝ))
    (hy2ne : y ≠ (block207S2 : ℝ))
    (hy3ne : y ≠ (block207S3 : ℝ))
    (hy4ne : y ≠ (block207S4 : ℝ)) :
    0 < block207V y := by
  by_cases h0 : y ≤ (block207RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block207RightChunk000L : ℝ) (block207RightChunk000R : ℝ) := by
      have hL : (block207RightChunk000L : ℝ) = (block207RightL : ℝ) := by
        norm_num [block207RightChunk000L, block207RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block207_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block207RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block207RightChunk001L : ℝ) (block207RightChunk001R : ℝ) := by
        have hprev : (block207RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block207RightChunk001L : ℝ) = (block207RightChunk000R : ℝ) := by
          norm_num [block207RightChunk001L, block207RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block207_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block207RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block207RightChunk002L : ℝ) (block207RightChunk002R : ℝ) := by
          have hprev : (block207RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block207RightChunk002L : ℝ) = (block207RightChunk001R : ℝ) := by
            norm_num [block207RightChunk002L, block207RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block207_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block207RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block207RightChunk003L : ℝ) = (block207RightChunk002R : ℝ) := by
          norm_num [block207RightChunk003L, block207RightChunk002R]
        have hR : (block207RightChunk003R : ℝ) = (block207RightR : ℝ) := by
          norm_num [block207RightChunk003R, block207RightR]
        have hyc : y ∈ Icc (block207RightChunk003L : ℝ) (block207RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block207_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block207_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block207LeftL : ℝ) (block207LeftR : ℝ) →
    y ≠ 0 → y ≠ (block207S1 : ℝ) → y ≠ (block207S2 : ℝ) →
    y ≠ (block207S3 : ℝ) → y ≠ (block207S4 : ℝ) → 0 < block207V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block207RightL : ℝ) (block207RightR : ℝ) →
    y ≠ 0 → y ≠ (block207S1 : ℝ) → y ≠ (block207S2 : ℝ) →
    y ≠ (block207S3 : ℝ) → y ≠ (block207S4 : ℝ) → 0 < block207V y)

theorem block207_reallog_certificate_proof :
    block207_reallog_certificate := by
  exact ⟨block207_left_V_pos, block207_right_V_pos⟩

end Block207
end M1817475
end Erdos1038Lean
