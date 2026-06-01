import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block210

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block210

open Set

def block210W1 : Rat := ((1207657434414761 : Rat) / 1250000000000000)
def block210W2 : Rat := ((1327340378585471 : Rat) / 25000000000000000)
def block210W3 : Rat := ((17517941697804967 : Rat) / 100000000000000000)
def block210W4 : Rat := ((152180561620671 : Rat) / 1562500000000000)
def block210S1 : Rat := ((18174751 : Rat) / 10000000)
def block210S2 : Rat := ((511587 : Rat) / 200000)
def block210S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block210S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block210V (y : ℝ) : ℝ :=
  ratPotential block210W1 block210W2 block210W3 block210W4 block210S1 block210S2 block210S3 block210S4 y

def block210LeftParamsCertificate : Bool :=
  allBoxesSameParams block210LeftBoxes block210W1 block210W2 block210W3 block210W4 block210S1 block210S2 block210S3 block210S4

theorem block210LeftParamsCertificate_eq_true :
    block210LeftParamsCertificate = true := by
  native_decide

theorem block210_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block210LeftL : ℝ) (block210LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block210S1 : ℝ))
    (hy2ne : y ≠ (block210S2 : ℝ))
    (hy3ne : y ≠ (block210S3 : ℝ))
    (hy4ne : y ≠ (block210S4 : ℝ)) :
    0 < block210V y := by
  have hcert := block210LeftCertificate_eq_true
  unfold block210LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block210LeftBoxes) (lo := block210LeftL) (hi := block210LeftR)
    (w1 := block210W1) (w2 := block210W2) (w3 := block210W3) (w4 := block210W4)
    (s1 := block210S1) (s2 := block210S2) (s3 := block210S3) (s4 := block210S4)
    hboxes hcover block210LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block210RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block210RightChunk000 block210W1 block210W2 block210W3 block210W4 block210S1 block210S2 block210S3 block210S4

theorem block210RightChunk000ParamsCertificate_eq_true :
    block210RightChunk000ParamsCertificate = true := by
  native_decide

theorem block210_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block210RightChunk000L : ℝ) (block210RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block210S1 : ℝ))
    (hy2ne : y ≠ (block210S2 : ℝ))
    (hy3ne : y ≠ (block210S3 : ℝ))
    (hy4ne : y ≠ (block210S4 : ℝ)) :
    0 < block210V y := by
  have hcert := block210RightChunk000Certificate_eq_true
  unfold block210RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block210RightChunk000) (lo := block210RightChunk000L) (hi := block210RightChunk000R)
    (w1 := block210W1) (w2 := block210W2) (w3 := block210W3) (w4 := block210W4)
    (s1 := block210S1) (s2 := block210S2) (s3 := block210S3) (s4 := block210S4)
    hboxes hcover block210RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block210RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block210RightChunk001 block210W1 block210W2 block210W3 block210W4 block210S1 block210S2 block210S3 block210S4

theorem block210RightChunk001ParamsCertificate_eq_true :
    block210RightChunk001ParamsCertificate = true := by
  native_decide

theorem block210_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block210RightChunk001L : ℝ) (block210RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block210S1 : ℝ))
    (hy2ne : y ≠ (block210S2 : ℝ))
    (hy3ne : y ≠ (block210S3 : ℝ))
    (hy4ne : y ≠ (block210S4 : ℝ)) :
    0 < block210V y := by
  have hcert := block210RightChunk001Certificate_eq_true
  unfold block210RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block210RightChunk001) (lo := block210RightChunk001L) (hi := block210RightChunk001R)
    (w1 := block210W1) (w2 := block210W2) (w3 := block210W3) (w4 := block210W4)
    (s1 := block210S1) (s2 := block210S2) (s3 := block210S3) (s4 := block210S4)
    hboxes hcover block210RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block210RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block210RightChunk002 block210W1 block210W2 block210W3 block210W4 block210S1 block210S2 block210S3 block210S4

theorem block210RightChunk002ParamsCertificate_eq_true :
    block210RightChunk002ParamsCertificate = true := by
  native_decide

theorem block210_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block210RightChunk002L : ℝ) (block210RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block210S1 : ℝ))
    (hy2ne : y ≠ (block210S2 : ℝ))
    (hy3ne : y ≠ (block210S3 : ℝ))
    (hy4ne : y ≠ (block210S4 : ℝ)) :
    0 < block210V y := by
  have hcert := block210RightChunk002Certificate_eq_true
  unfold block210RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block210RightChunk002) (lo := block210RightChunk002L) (hi := block210RightChunk002R)
    (w1 := block210W1) (w2 := block210W2) (w3 := block210W3) (w4 := block210W4)
    (s1 := block210S1) (s2 := block210S2) (s3 := block210S3) (s4 := block210S4)
    hboxes hcover block210RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block210RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block210RightChunk003 block210W1 block210W2 block210W3 block210W4 block210S1 block210S2 block210S3 block210S4

theorem block210RightChunk003ParamsCertificate_eq_true :
    block210RightChunk003ParamsCertificate = true := by
  native_decide

theorem block210_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block210RightChunk003L : ℝ) (block210RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block210S1 : ℝ))
    (hy2ne : y ≠ (block210S2 : ℝ))
    (hy3ne : y ≠ (block210S3 : ℝ))
    (hy4ne : y ≠ (block210S4 : ℝ)) :
    0 < block210V y := by
  have hcert := block210RightChunk003Certificate_eq_true
  unfold block210RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block210RightChunk003) (lo := block210RightChunk003L) (hi := block210RightChunk003R)
    (w1 := block210W1) (w2 := block210W2) (w3 := block210W3) (w4 := block210W4)
    (s1 := block210S1) (s2 := block210S2) (s3 := block210S3) (s4 := block210S4)
    hboxes hcover block210RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block210_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block210RightL : ℝ) (block210RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block210S1 : ℝ))
    (hy2ne : y ≠ (block210S2 : ℝ))
    (hy3ne : y ≠ (block210S3 : ℝ))
    (hy4ne : y ≠ (block210S4 : ℝ)) :
    0 < block210V y := by
  by_cases h0 : y ≤ (block210RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block210RightChunk000L : ℝ) (block210RightChunk000R : ℝ) := by
      have hL : (block210RightChunk000L : ℝ) = (block210RightL : ℝ) := by
        norm_num [block210RightChunk000L, block210RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block210_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block210RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block210RightChunk001L : ℝ) (block210RightChunk001R : ℝ) := by
        have hprev : (block210RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block210RightChunk001L : ℝ) = (block210RightChunk000R : ℝ) := by
          norm_num [block210RightChunk001L, block210RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block210_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block210RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block210RightChunk002L : ℝ) (block210RightChunk002R : ℝ) := by
          have hprev : (block210RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block210RightChunk002L : ℝ) = (block210RightChunk001R : ℝ) := by
            norm_num [block210RightChunk002L, block210RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block210_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block210RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block210RightChunk003L : ℝ) = (block210RightChunk002R : ℝ) := by
          norm_num [block210RightChunk003L, block210RightChunk002R]
        have hR : (block210RightChunk003R : ℝ) = (block210RightR : ℝ) := by
          norm_num [block210RightChunk003R, block210RightR]
        have hyc : y ∈ Icc (block210RightChunk003L : ℝ) (block210RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block210_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block210_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block210LeftL : ℝ) (block210LeftR : ℝ) →
    y ≠ 0 → y ≠ (block210S1 : ℝ) → y ≠ (block210S2 : ℝ) →
    y ≠ (block210S3 : ℝ) → y ≠ (block210S4 : ℝ) → 0 < block210V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block210RightL : ℝ) (block210RightR : ℝ) →
    y ≠ 0 → y ≠ (block210S1 : ℝ) → y ≠ (block210S2 : ℝ) →
    y ≠ (block210S3 : ℝ) → y ≠ (block210S4 : ℝ) → 0 < block210V y)

theorem block210_reallog_certificate_proof :
    block210_reallog_certificate := by
  exact ⟨block210_left_V_pos, block210_right_V_pos⟩

end Block210
end M1817475
end Erdos1038Lean
