import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block211

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block211

open Set

def block211W1 : Rat := ((9659266087950789 : Rat) / 10000000000000000)
def block211W2 : Rat := ((10632915003199049 : Rat) / 200000000000000000)
def block211W3 : Rat := ((875460596438083 : Rat) / 5000000000000000)
def block211W4 : Rat := ((2436040901337171 : Rat) / 25000000000000000)
def block211S1 : Rat := ((18174751 : Rat) / 10000000)
def block211S2 : Rat := ((511587 : Rat) / 200000)
def block211S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block211S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block211V (y : ℝ) : ℝ :=
  ratPotential block211W1 block211W2 block211W3 block211W4 block211S1 block211S2 block211S3 block211S4 y

def block211LeftParamsCertificate : Bool :=
  allBoxesSameParams block211LeftBoxes block211W1 block211W2 block211W3 block211W4 block211S1 block211S2 block211S3 block211S4

theorem block211LeftParamsCertificate_eq_true :
    block211LeftParamsCertificate = true := by
  native_decide

theorem block211_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block211LeftL : ℝ) (block211LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block211S1 : ℝ))
    (hy2ne : y ≠ (block211S2 : ℝ))
    (hy3ne : y ≠ (block211S3 : ℝ))
    (hy4ne : y ≠ (block211S4 : ℝ)) :
    0 < block211V y := by
  have hcert := block211LeftCertificate_eq_true
  unfold block211LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block211LeftBoxes) (lo := block211LeftL) (hi := block211LeftR)
    (w1 := block211W1) (w2 := block211W2) (w3 := block211W3) (w4 := block211W4)
    (s1 := block211S1) (s2 := block211S2) (s3 := block211S3) (s4 := block211S4)
    hboxes hcover block211LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block211RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block211RightChunk000 block211W1 block211W2 block211W3 block211W4 block211S1 block211S2 block211S3 block211S4

theorem block211RightChunk000ParamsCertificate_eq_true :
    block211RightChunk000ParamsCertificate = true := by
  native_decide

theorem block211_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block211RightChunk000L : ℝ) (block211RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block211S1 : ℝ))
    (hy2ne : y ≠ (block211S2 : ℝ))
    (hy3ne : y ≠ (block211S3 : ℝ))
    (hy4ne : y ≠ (block211S4 : ℝ)) :
    0 < block211V y := by
  have hcert := block211RightChunk000Certificate_eq_true
  unfold block211RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block211RightChunk000) (lo := block211RightChunk000L) (hi := block211RightChunk000R)
    (w1 := block211W1) (w2 := block211W2) (w3 := block211W3) (w4 := block211W4)
    (s1 := block211S1) (s2 := block211S2) (s3 := block211S3) (s4 := block211S4)
    hboxes hcover block211RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block211RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block211RightChunk001 block211W1 block211W2 block211W3 block211W4 block211S1 block211S2 block211S3 block211S4

theorem block211RightChunk001ParamsCertificate_eq_true :
    block211RightChunk001ParamsCertificate = true := by
  native_decide

theorem block211_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block211RightChunk001L : ℝ) (block211RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block211S1 : ℝ))
    (hy2ne : y ≠ (block211S2 : ℝ))
    (hy3ne : y ≠ (block211S3 : ℝ))
    (hy4ne : y ≠ (block211S4 : ℝ)) :
    0 < block211V y := by
  have hcert := block211RightChunk001Certificate_eq_true
  unfold block211RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block211RightChunk001) (lo := block211RightChunk001L) (hi := block211RightChunk001R)
    (w1 := block211W1) (w2 := block211W2) (w3 := block211W3) (w4 := block211W4)
    (s1 := block211S1) (s2 := block211S2) (s3 := block211S3) (s4 := block211S4)
    hboxes hcover block211RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block211RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block211RightChunk002 block211W1 block211W2 block211W3 block211W4 block211S1 block211S2 block211S3 block211S4

theorem block211RightChunk002ParamsCertificate_eq_true :
    block211RightChunk002ParamsCertificate = true := by
  native_decide

theorem block211_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block211RightChunk002L : ℝ) (block211RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block211S1 : ℝ))
    (hy2ne : y ≠ (block211S2 : ℝ))
    (hy3ne : y ≠ (block211S3 : ℝ))
    (hy4ne : y ≠ (block211S4 : ℝ)) :
    0 < block211V y := by
  have hcert := block211RightChunk002Certificate_eq_true
  unfold block211RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block211RightChunk002) (lo := block211RightChunk002L) (hi := block211RightChunk002R)
    (w1 := block211W1) (w2 := block211W2) (w3 := block211W3) (w4 := block211W4)
    (s1 := block211S1) (s2 := block211S2) (s3 := block211S3) (s4 := block211S4)
    hboxes hcover block211RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block211RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block211RightChunk003 block211W1 block211W2 block211W3 block211W4 block211S1 block211S2 block211S3 block211S4

theorem block211RightChunk003ParamsCertificate_eq_true :
    block211RightChunk003ParamsCertificate = true := by
  native_decide

theorem block211_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block211RightChunk003L : ℝ) (block211RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block211S1 : ℝ))
    (hy2ne : y ≠ (block211S2 : ℝ))
    (hy3ne : y ≠ (block211S3 : ℝ))
    (hy4ne : y ≠ (block211S4 : ℝ)) :
    0 < block211V y := by
  have hcert := block211RightChunk003Certificate_eq_true
  unfold block211RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block211RightChunk003) (lo := block211RightChunk003L) (hi := block211RightChunk003R)
    (w1 := block211W1) (w2 := block211W2) (w3 := block211W3) (w4 := block211W4)
    (s1 := block211S1) (s2 := block211S2) (s3 := block211S3) (s4 := block211S4)
    hboxes hcover block211RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block211_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block211RightL : ℝ) (block211RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block211S1 : ℝ))
    (hy2ne : y ≠ (block211S2 : ℝ))
    (hy3ne : y ≠ (block211S3 : ℝ))
    (hy4ne : y ≠ (block211S4 : ℝ)) :
    0 < block211V y := by
  by_cases h0 : y ≤ (block211RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block211RightChunk000L : ℝ) (block211RightChunk000R : ℝ) := by
      have hL : (block211RightChunk000L : ℝ) = (block211RightL : ℝ) := by
        norm_num [block211RightChunk000L, block211RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block211_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block211RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block211RightChunk001L : ℝ) (block211RightChunk001R : ℝ) := by
        have hprev : (block211RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block211RightChunk001L : ℝ) = (block211RightChunk000R : ℝ) := by
          norm_num [block211RightChunk001L, block211RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block211_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block211RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block211RightChunk002L : ℝ) (block211RightChunk002R : ℝ) := by
          have hprev : (block211RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block211RightChunk002L : ℝ) = (block211RightChunk001R : ℝ) := by
            norm_num [block211RightChunk002L, block211RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block211_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block211RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block211RightChunk003L : ℝ) = (block211RightChunk002R : ℝ) := by
          norm_num [block211RightChunk003L, block211RightChunk002R]
        have hR : (block211RightChunk003R : ℝ) = (block211RightR : ℝ) := by
          norm_num [block211RightChunk003R, block211RightR]
        have hyc : y ∈ Icc (block211RightChunk003L : ℝ) (block211RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block211_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block211_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block211LeftL : ℝ) (block211LeftR : ℝ) →
    y ≠ 0 → y ≠ (block211S1 : ℝ) → y ≠ (block211S2 : ℝ) →
    y ≠ (block211S3 : ℝ) → y ≠ (block211S4 : ℝ) → 0 < block211V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block211RightL : ℝ) (block211RightR : ℝ) →
    y ≠ 0 → y ≠ (block211S1 : ℝ) → y ≠ (block211S2 : ℝ) →
    y ≠ (block211S3 : ℝ) → y ≠ (block211S4 : ℝ) → 0 < block211V y)

theorem block211_reallog_certificate_proof :
    block211_reallog_certificate := by
  exact ⟨block211_left_V_pos, block211_right_V_pos⟩

end Block211
end M1817475
end Erdos1038Lean
