import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block214

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block214

open Set

def block214W1 : Rat := ((9638573447707797 : Rat) / 10000000000000000)
def block214W2 : Rat := ((336328248830749 : Rat) / 6250000000000000)
def block214W3 : Rat := ((17425230026503213 : Rat) / 100000000000000000)
def block214W4 : Rat := ((4892561078396257 : Rat) / 50000000000000000)
def block214S1 : Rat := ((18174751 : Rat) / 10000000)
def block214S2 : Rat := ((511587 : Rat) / 200000)
def block214S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block214S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block214V (y : ℝ) : ℝ :=
  ratPotential block214W1 block214W2 block214W3 block214W4 block214S1 block214S2 block214S3 block214S4 y

def block214LeftParamsCertificate : Bool :=
  allBoxesSameParams block214LeftBoxes block214W1 block214W2 block214W3 block214W4 block214S1 block214S2 block214S3 block214S4

theorem block214LeftParamsCertificate_eq_true :
    block214LeftParamsCertificate = true := by
  native_decide

theorem block214_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block214LeftL : ℝ) (block214LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block214S1 : ℝ))
    (hy2ne : y ≠ (block214S2 : ℝ))
    (hy3ne : y ≠ (block214S3 : ℝ))
    (hy4ne : y ≠ (block214S4 : ℝ)) :
    0 < block214V y := by
  have hcert := block214LeftCertificate_eq_true
  unfold block214LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block214LeftBoxes) (lo := block214LeftL) (hi := block214LeftR)
    (w1 := block214W1) (w2 := block214W2) (w3 := block214W3) (w4 := block214W4)
    (s1 := block214S1) (s2 := block214S2) (s3 := block214S3) (s4 := block214S4)
    hboxes hcover block214LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block214RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block214RightChunk000 block214W1 block214W2 block214W3 block214W4 block214S1 block214S2 block214S3 block214S4

theorem block214RightChunk000ParamsCertificate_eq_true :
    block214RightChunk000ParamsCertificate = true := by
  native_decide

theorem block214_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block214RightChunk000L : ℝ) (block214RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block214S1 : ℝ))
    (hy2ne : y ≠ (block214S2 : ℝ))
    (hy3ne : y ≠ (block214S3 : ℝ))
    (hy4ne : y ≠ (block214S4 : ℝ)) :
    0 < block214V y := by
  have hcert := block214RightChunk000Certificate_eq_true
  unfold block214RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block214RightChunk000) (lo := block214RightChunk000L) (hi := block214RightChunk000R)
    (w1 := block214W1) (w2 := block214W2) (w3 := block214W3) (w4 := block214W4)
    (s1 := block214S1) (s2 := block214S2) (s3 := block214S3) (s4 := block214S4)
    hboxes hcover block214RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block214RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block214RightChunk001 block214W1 block214W2 block214W3 block214W4 block214S1 block214S2 block214S3 block214S4

theorem block214RightChunk001ParamsCertificate_eq_true :
    block214RightChunk001ParamsCertificate = true := by
  native_decide

theorem block214_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block214RightChunk001L : ℝ) (block214RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block214S1 : ℝ))
    (hy2ne : y ≠ (block214S2 : ℝ))
    (hy3ne : y ≠ (block214S3 : ℝ))
    (hy4ne : y ≠ (block214S4 : ℝ)) :
    0 < block214V y := by
  have hcert := block214RightChunk001Certificate_eq_true
  unfold block214RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block214RightChunk001) (lo := block214RightChunk001L) (hi := block214RightChunk001R)
    (w1 := block214W1) (w2 := block214W2) (w3 := block214W3) (w4 := block214W4)
    (s1 := block214S1) (s2 := block214S2) (s3 := block214S3) (s4 := block214S4)
    hboxes hcover block214RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block214RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block214RightChunk002 block214W1 block214W2 block214W3 block214W4 block214S1 block214S2 block214S3 block214S4

theorem block214RightChunk002ParamsCertificate_eq_true :
    block214RightChunk002ParamsCertificate = true := by
  native_decide

theorem block214_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block214RightChunk002L : ℝ) (block214RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block214S1 : ℝ))
    (hy2ne : y ≠ (block214S2 : ℝ))
    (hy3ne : y ≠ (block214S3 : ℝ))
    (hy4ne : y ≠ (block214S4 : ℝ)) :
    0 < block214V y := by
  have hcert := block214RightChunk002Certificate_eq_true
  unfold block214RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block214RightChunk002) (lo := block214RightChunk002L) (hi := block214RightChunk002R)
    (w1 := block214W1) (w2 := block214W2) (w3 := block214W3) (w4 := block214W4)
    (s1 := block214S1) (s2 := block214S2) (s3 := block214S3) (s4 := block214S4)
    hboxes hcover block214RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block214RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block214RightChunk003 block214W1 block214W2 block214W3 block214W4 block214S1 block214S2 block214S3 block214S4

theorem block214RightChunk003ParamsCertificate_eq_true :
    block214RightChunk003ParamsCertificate = true := by
  native_decide

theorem block214_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block214RightChunk003L : ℝ) (block214RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block214S1 : ℝ))
    (hy2ne : y ≠ (block214S2 : ℝ))
    (hy3ne : y ≠ (block214S3 : ℝ))
    (hy4ne : y ≠ (block214S4 : ℝ)) :
    0 < block214V y := by
  have hcert := block214RightChunk003Certificate_eq_true
  unfold block214RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block214RightChunk003) (lo := block214RightChunk003L) (hi := block214RightChunk003R)
    (w1 := block214W1) (w2 := block214W2) (w3 := block214W3) (w4 := block214W4)
    (s1 := block214S1) (s2 := block214S2) (s3 := block214S3) (s4 := block214S4)
    hboxes hcover block214RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block214_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block214RightL : ℝ) (block214RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block214S1 : ℝ))
    (hy2ne : y ≠ (block214S2 : ℝ))
    (hy3ne : y ≠ (block214S3 : ℝ))
    (hy4ne : y ≠ (block214S4 : ℝ)) :
    0 < block214V y := by
  by_cases h0 : y ≤ (block214RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block214RightChunk000L : ℝ) (block214RightChunk000R : ℝ) := by
      have hL : (block214RightChunk000L : ℝ) = (block214RightL : ℝ) := by
        norm_num [block214RightChunk000L, block214RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block214_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block214RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block214RightChunk001L : ℝ) (block214RightChunk001R : ℝ) := by
        have hprev : (block214RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block214RightChunk001L : ℝ) = (block214RightChunk000R : ℝ) := by
          norm_num [block214RightChunk001L, block214RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block214_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block214RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block214RightChunk002L : ℝ) (block214RightChunk002R : ℝ) := by
          have hprev : (block214RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block214RightChunk002L : ℝ) = (block214RightChunk001R : ℝ) := by
            norm_num [block214RightChunk002L, block214RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block214_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block214RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block214RightChunk003L : ℝ) = (block214RightChunk002R : ℝ) := by
          norm_num [block214RightChunk003L, block214RightChunk002R]
        have hR : (block214RightChunk003R : ℝ) = (block214RightR : ℝ) := by
          norm_num [block214RightChunk003R, block214RightR]
        have hyc : y ∈ Icc (block214RightChunk003L : ℝ) (block214RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block214_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block214_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block214LeftL : ℝ) (block214LeftR : ℝ) →
    y ≠ 0 → y ≠ (block214S1 : ℝ) → y ≠ (block214S2 : ℝ) →
    y ≠ (block214S3 : ℝ) → y ≠ (block214S4 : ℝ) → 0 < block214V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block214RightL : ℝ) (block214RightR : ℝ) →
    y ≠ 0 → y ≠ (block214S1 : ℝ) → y ≠ (block214S2 : ℝ) →
    y ≠ (block214S3 : ℝ) → y ≠ (block214S4 : ℝ) → 0 < block214V y)

theorem block214_reallog_certificate_proof :
    block214_reallog_certificate := by
  exact ⟨block214_left_V_pos, block214_right_V_pos⟩

end Block214
end M1817475
end Erdos1038Lean
