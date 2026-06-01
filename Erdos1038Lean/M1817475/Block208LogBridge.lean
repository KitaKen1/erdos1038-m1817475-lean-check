import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block208

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block208

open Set

def block208W1 : Rat := ((9677077239348543 : Rat) / 10000000000000000)
def block208W2 : Rat := ((13151002921835431 : Rat) / 250000000000000000)
def block208W3 : Rat := ((1758178292734153 : Rat) / 10000000000000000)
def block208W4 : Rat := ((4854306449491909 : Rat) / 50000000000000000)
def block208S1 : Rat := ((18174751 : Rat) / 10000000)
def block208S2 : Rat := ((511587 : Rat) / 200000)
def block208S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block208S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block208V (y : ℝ) : ℝ :=
  ratPotential block208W1 block208W2 block208W3 block208W4 block208S1 block208S2 block208S3 block208S4 y

def block208LeftParamsCertificate : Bool :=
  allBoxesSameParams block208LeftBoxes block208W1 block208W2 block208W3 block208W4 block208S1 block208S2 block208S3 block208S4

theorem block208LeftParamsCertificate_eq_true :
    block208LeftParamsCertificate = true := by
  native_decide

theorem block208_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block208LeftL : ℝ) (block208LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block208S1 : ℝ))
    (hy2ne : y ≠ (block208S2 : ℝ))
    (hy3ne : y ≠ (block208S3 : ℝ))
    (hy4ne : y ≠ (block208S4 : ℝ)) :
    0 < block208V y := by
  have hcert := block208LeftCertificate_eq_true
  unfold block208LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block208LeftBoxes) (lo := block208LeftL) (hi := block208LeftR)
    (w1 := block208W1) (w2 := block208W2) (w3 := block208W3) (w4 := block208W4)
    (s1 := block208S1) (s2 := block208S2) (s3 := block208S3) (s4 := block208S4)
    hboxes hcover block208LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block208RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block208RightChunk000 block208W1 block208W2 block208W3 block208W4 block208S1 block208S2 block208S3 block208S4

theorem block208RightChunk000ParamsCertificate_eq_true :
    block208RightChunk000ParamsCertificate = true := by
  native_decide

theorem block208_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block208RightChunk000L : ℝ) (block208RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block208S1 : ℝ))
    (hy2ne : y ≠ (block208S2 : ℝ))
    (hy3ne : y ≠ (block208S3 : ℝ))
    (hy4ne : y ≠ (block208S4 : ℝ)) :
    0 < block208V y := by
  have hcert := block208RightChunk000Certificate_eq_true
  unfold block208RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block208RightChunk000) (lo := block208RightChunk000L) (hi := block208RightChunk000R)
    (w1 := block208W1) (w2 := block208W2) (w3 := block208W3) (w4 := block208W4)
    (s1 := block208S1) (s2 := block208S2) (s3 := block208S3) (s4 := block208S4)
    hboxes hcover block208RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block208RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block208RightChunk001 block208W1 block208W2 block208W3 block208W4 block208S1 block208S2 block208S3 block208S4

theorem block208RightChunk001ParamsCertificate_eq_true :
    block208RightChunk001ParamsCertificate = true := by
  native_decide

theorem block208_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block208RightChunk001L : ℝ) (block208RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block208S1 : ℝ))
    (hy2ne : y ≠ (block208S2 : ℝ))
    (hy3ne : y ≠ (block208S3 : ℝ))
    (hy4ne : y ≠ (block208S4 : ℝ)) :
    0 < block208V y := by
  have hcert := block208RightChunk001Certificate_eq_true
  unfold block208RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block208RightChunk001) (lo := block208RightChunk001L) (hi := block208RightChunk001R)
    (w1 := block208W1) (w2 := block208W2) (w3 := block208W3) (w4 := block208W4)
    (s1 := block208S1) (s2 := block208S2) (s3 := block208S3) (s4 := block208S4)
    hboxes hcover block208RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block208RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block208RightChunk002 block208W1 block208W2 block208W3 block208W4 block208S1 block208S2 block208S3 block208S4

theorem block208RightChunk002ParamsCertificate_eq_true :
    block208RightChunk002ParamsCertificate = true := by
  native_decide

theorem block208_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block208RightChunk002L : ℝ) (block208RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block208S1 : ℝ))
    (hy2ne : y ≠ (block208S2 : ℝ))
    (hy3ne : y ≠ (block208S3 : ℝ))
    (hy4ne : y ≠ (block208S4 : ℝ)) :
    0 < block208V y := by
  have hcert := block208RightChunk002Certificate_eq_true
  unfold block208RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block208RightChunk002) (lo := block208RightChunk002L) (hi := block208RightChunk002R)
    (w1 := block208W1) (w2 := block208W2) (w3 := block208W3) (w4 := block208W4)
    (s1 := block208S1) (s2 := block208S2) (s3 := block208S3) (s4 := block208S4)
    hboxes hcover block208RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block208RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block208RightChunk003 block208W1 block208W2 block208W3 block208W4 block208S1 block208S2 block208S3 block208S4

theorem block208RightChunk003ParamsCertificate_eq_true :
    block208RightChunk003ParamsCertificate = true := by
  native_decide

theorem block208_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block208RightChunk003L : ℝ) (block208RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block208S1 : ℝ))
    (hy2ne : y ≠ (block208S2 : ℝ))
    (hy3ne : y ≠ (block208S3 : ℝ))
    (hy4ne : y ≠ (block208S4 : ℝ)) :
    0 < block208V y := by
  have hcert := block208RightChunk003Certificate_eq_true
  unfold block208RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block208RightChunk003) (lo := block208RightChunk003L) (hi := block208RightChunk003R)
    (w1 := block208W1) (w2 := block208W2) (w3 := block208W3) (w4 := block208W4)
    (s1 := block208S1) (s2 := block208S2) (s3 := block208S3) (s4 := block208S4)
    hboxes hcover block208RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block208_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block208RightL : ℝ) (block208RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block208S1 : ℝ))
    (hy2ne : y ≠ (block208S2 : ℝ))
    (hy3ne : y ≠ (block208S3 : ℝ))
    (hy4ne : y ≠ (block208S4 : ℝ)) :
    0 < block208V y := by
  by_cases h0 : y ≤ (block208RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block208RightChunk000L : ℝ) (block208RightChunk000R : ℝ) := by
      have hL : (block208RightChunk000L : ℝ) = (block208RightL : ℝ) := by
        norm_num [block208RightChunk000L, block208RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block208_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block208RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block208RightChunk001L : ℝ) (block208RightChunk001R : ℝ) := by
        have hprev : (block208RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block208RightChunk001L : ℝ) = (block208RightChunk000R : ℝ) := by
          norm_num [block208RightChunk001L, block208RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block208_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block208RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block208RightChunk002L : ℝ) (block208RightChunk002R : ℝ) := by
          have hprev : (block208RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block208RightChunk002L : ℝ) = (block208RightChunk001R : ℝ) := by
            norm_num [block208RightChunk002L, block208RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block208_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block208RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block208RightChunk003L : ℝ) = (block208RightChunk002R : ℝ) := by
          norm_num [block208RightChunk003L, block208RightChunk002R]
        have hR : (block208RightChunk003R : ℝ) = (block208RightR : ℝ) := by
          norm_num [block208RightChunk003R, block208RightR]
        have hyc : y ∈ Icc (block208RightChunk003L : ℝ) (block208RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block208_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block208_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block208LeftL : ℝ) (block208LeftR : ℝ) →
    y ≠ 0 → y ≠ (block208S1 : ℝ) → y ≠ (block208S2 : ℝ) →
    y ≠ (block208S3 : ℝ) → y ≠ (block208S4 : ℝ) → 0 < block208V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block208RightL : ℝ) (block208RightR : ℝ) →
    y ≠ 0 → y ≠ (block208S1 : ℝ) → y ≠ (block208S2 : ℝ) →
    y ≠ (block208S3 : ℝ) → y ≠ (block208S4 : ℝ) → 0 < block208V y)

theorem block208_reallog_certificate_proof :
    block208_reallog_certificate := by
  exact ⟨block208_left_V_pos, block208_right_V_pos⟩

end Block208
end M1817475
end Erdos1038Lean
