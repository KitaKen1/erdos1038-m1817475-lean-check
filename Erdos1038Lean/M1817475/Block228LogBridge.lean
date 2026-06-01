import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block228

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block228

open Set

def block228W1 : Rat := ((9551286665243841 : Rat) / 10000000000000000)
def block228W2 : Rat := ((5659469422265223 : Rat) / 100000000000000000)
def block228W3 : Rat := ((17068262336637433 : Rat) / 100000000000000000)
def block228W4 : Rat := ((9960589261582037 : Rat) / 100000000000000000)
def block228S1 : Rat := ((18174751 : Rat) / 10000000)
def block228S2 : Rat := ((511587 : Rat) / 200000)
def block228S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block228S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block228V (y : ℝ) : ℝ :=
  ratPotential block228W1 block228W2 block228W3 block228W4 block228S1 block228S2 block228S3 block228S4 y

def block228LeftParamsCertificate : Bool :=
  allBoxesSameParams block228LeftBoxes block228W1 block228W2 block228W3 block228W4 block228S1 block228S2 block228S3 block228S4

theorem block228LeftParamsCertificate_eq_true :
    block228LeftParamsCertificate = true := by
  native_decide

theorem block228_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block228LeftL : ℝ) (block228LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block228S1 : ℝ))
    (hy2ne : y ≠ (block228S2 : ℝ))
    (hy3ne : y ≠ (block228S3 : ℝ))
    (hy4ne : y ≠ (block228S4 : ℝ)) :
    0 < block228V y := by
  have hcert := block228LeftCertificate_eq_true
  unfold block228LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block228LeftBoxes) (lo := block228LeftL) (hi := block228LeftR)
    (w1 := block228W1) (w2 := block228W2) (w3 := block228W3) (w4 := block228W4)
    (s1 := block228S1) (s2 := block228S2) (s3 := block228S3) (s4 := block228S4)
    hboxes hcover block228LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block228RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block228RightChunk000 block228W1 block228W2 block228W3 block228W4 block228S1 block228S2 block228S3 block228S4

theorem block228RightChunk000ParamsCertificate_eq_true :
    block228RightChunk000ParamsCertificate = true := by
  native_decide

theorem block228_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block228RightChunk000L : ℝ) (block228RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block228S1 : ℝ))
    (hy2ne : y ≠ (block228S2 : ℝ))
    (hy3ne : y ≠ (block228S3 : ℝ))
    (hy4ne : y ≠ (block228S4 : ℝ)) :
    0 < block228V y := by
  have hcert := block228RightChunk000Certificate_eq_true
  unfold block228RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block228RightChunk000) (lo := block228RightChunk000L) (hi := block228RightChunk000R)
    (w1 := block228W1) (w2 := block228W2) (w3 := block228W3) (w4 := block228W4)
    (s1 := block228S1) (s2 := block228S2) (s3 := block228S3) (s4 := block228S4)
    hboxes hcover block228RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block228RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block228RightChunk001 block228W1 block228W2 block228W3 block228W4 block228S1 block228S2 block228S3 block228S4

theorem block228RightChunk001ParamsCertificate_eq_true :
    block228RightChunk001ParamsCertificate = true := by
  native_decide

theorem block228_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block228RightChunk001L : ℝ) (block228RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block228S1 : ℝ))
    (hy2ne : y ≠ (block228S2 : ℝ))
    (hy3ne : y ≠ (block228S3 : ℝ))
    (hy4ne : y ≠ (block228S4 : ℝ)) :
    0 < block228V y := by
  have hcert := block228RightChunk001Certificate_eq_true
  unfold block228RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block228RightChunk001) (lo := block228RightChunk001L) (hi := block228RightChunk001R)
    (w1 := block228W1) (w2 := block228W2) (w3 := block228W3) (w4 := block228W4)
    (s1 := block228S1) (s2 := block228S2) (s3 := block228S3) (s4 := block228S4)
    hboxes hcover block228RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block228RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block228RightChunk002 block228W1 block228W2 block228W3 block228W4 block228S1 block228S2 block228S3 block228S4

theorem block228RightChunk002ParamsCertificate_eq_true :
    block228RightChunk002ParamsCertificate = true := by
  native_decide

theorem block228_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block228RightChunk002L : ℝ) (block228RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block228S1 : ℝ))
    (hy2ne : y ≠ (block228S2 : ℝ))
    (hy3ne : y ≠ (block228S3 : ℝ))
    (hy4ne : y ≠ (block228S4 : ℝ)) :
    0 < block228V y := by
  have hcert := block228RightChunk002Certificate_eq_true
  unfold block228RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block228RightChunk002) (lo := block228RightChunk002L) (hi := block228RightChunk002R)
    (w1 := block228W1) (w2 := block228W2) (w3 := block228W3) (w4 := block228W4)
    (s1 := block228S1) (s2 := block228S2) (s3 := block228S3) (s4 := block228S4)
    hboxes hcover block228RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block228_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block228RightL : ℝ) (block228RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block228S1 : ℝ))
    (hy2ne : y ≠ (block228S2 : ℝ))
    (hy3ne : y ≠ (block228S3 : ℝ))
    (hy4ne : y ≠ (block228S4 : ℝ)) :
    0 < block228V y := by
  by_cases h0 : y ≤ (block228RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block228RightChunk000L : ℝ) (block228RightChunk000R : ℝ) := by
      have hL : (block228RightChunk000L : ℝ) = (block228RightL : ℝ) := by
        norm_num [block228RightChunk000L, block228RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block228_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block228RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block228RightChunk001L : ℝ) (block228RightChunk001R : ℝ) := by
        have hprev : (block228RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block228RightChunk001L : ℝ) = (block228RightChunk000R : ℝ) := by
          norm_num [block228RightChunk001L, block228RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block228_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block228RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block228RightChunk002L : ℝ) = (block228RightChunk001R : ℝ) := by
        norm_num [block228RightChunk002L, block228RightChunk001R]
      have hR : (block228RightChunk002R : ℝ) = (block228RightR : ℝ) := by
        norm_num [block228RightChunk002R, block228RightR]
      have hyc : y ∈ Icc (block228RightChunk002L : ℝ) (block228RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block228_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block228_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block228LeftL : ℝ) (block228LeftR : ℝ) →
    y ≠ 0 → y ≠ (block228S1 : ℝ) → y ≠ (block228S2 : ℝ) →
    y ≠ (block228S3 : ℝ) → y ≠ (block228S4 : ℝ) → 0 < block228V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block228RightL : ℝ) (block228RightR : ℝ) →
    y ≠ 0 → y ≠ (block228S1 : ℝ) → y ≠ (block228S2 : ℝ) →
    y ≠ (block228S3 : ℝ) → y ≠ (block228S4 : ℝ) → 0 < block228V y)

theorem block228_reallog_certificate_proof :
    block228_reallog_certificate := by
  exact ⟨block228_left_V_pos, block228_right_V_pos⟩

end Block228
end M1817475
end Erdos1038Lean
