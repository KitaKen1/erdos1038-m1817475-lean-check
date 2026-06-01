import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block400

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block400

open Set

def block400W1 : Rat := ((3755087657499161 : Rat) / 5000000000000000)
def block400W2 : Rat := (0 : Rat)
def block400W3 : Rat := ((27634067272857477 : Rat) / 100000000000000000)
def block400W4 : Rat := ((1874884345741627 : Rat) / 20000000000000000)
def block400S1 : Rat := ((18174751 : Rat) / 10000000)
def block400S2 : Rat := ((511587 : Rat) / 200000)
def block400S3 : Rat := ((132313914375000000063 : Rat) / 50000000000000000000)
def block400S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block400V (y : ℝ) : ℝ :=
  ratPotential block400W1 block400W2 block400W3 block400W4 block400S1 block400S2 block400S3 block400S4 y

def block400LeftParamsCertificate : Bool :=
  allBoxesSameParams block400LeftBoxes block400W1 block400W2 block400W3 block400W4 block400S1 block400S2 block400S3 block400S4

theorem block400LeftParamsCertificate_eq_true :
    block400LeftParamsCertificate = true := by
  native_decide

theorem block400_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block400LeftL : ℝ) (block400LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block400S1 : ℝ))
    (hy2ne : y ≠ (block400S2 : ℝ))
    (hy3ne : y ≠ (block400S3 : ℝ))
    (hy4ne : y ≠ (block400S4 : ℝ)) :
    0 < block400V y := by
  have hcert := block400LeftCertificate_eq_true
  unfold block400LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block400LeftBoxes) (lo := block400LeftL) (hi := block400LeftR)
    (w1 := block400W1) (w2 := block400W2) (w3 := block400W3) (w4 := block400W4)
    (s1 := block400S1) (s2 := block400S2) (s3 := block400S3) (s4 := block400S4)
    hboxes hcover block400LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block400RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block400RightChunk000 block400W1 block400W2 block400W3 block400W4 block400S1 block400S2 block400S3 block400S4

theorem block400RightChunk000ParamsCertificate_eq_true :
    block400RightChunk000ParamsCertificate = true := by
  native_decide

theorem block400_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block400RightChunk000L : ℝ) (block400RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block400S1 : ℝ))
    (hy2ne : y ≠ (block400S2 : ℝ))
    (hy3ne : y ≠ (block400S3 : ℝ))
    (hy4ne : y ≠ (block400S4 : ℝ)) :
    0 < block400V y := by
  have hcert := block400RightChunk000Certificate_eq_true
  unfold block400RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block400RightChunk000) (lo := block400RightChunk000L) (hi := block400RightChunk000R)
    (w1 := block400W1) (w2 := block400W2) (w3 := block400W3) (w4 := block400W4)
    (s1 := block400S1) (s2 := block400S2) (s3 := block400S3) (s4 := block400S4)
    hboxes hcover block400RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block400RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block400RightChunk001 block400W1 block400W2 block400W3 block400W4 block400S1 block400S2 block400S3 block400S4

theorem block400RightChunk001ParamsCertificate_eq_true :
    block400RightChunk001ParamsCertificate = true := by
  native_decide

theorem block400_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block400RightChunk001L : ℝ) (block400RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block400S1 : ℝ))
    (hy2ne : y ≠ (block400S2 : ℝ))
    (hy3ne : y ≠ (block400S3 : ℝ))
    (hy4ne : y ≠ (block400S4 : ℝ)) :
    0 < block400V y := by
  have hcert := block400RightChunk001Certificate_eq_true
  unfold block400RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block400RightChunk001) (lo := block400RightChunk001L) (hi := block400RightChunk001R)
    (w1 := block400W1) (w2 := block400W2) (w3 := block400W3) (w4 := block400W4)
    (s1 := block400S1) (s2 := block400S2) (s3 := block400S3) (s4 := block400S4)
    hboxes hcover block400RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block400RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block400RightChunk002 block400W1 block400W2 block400W3 block400W4 block400S1 block400S2 block400S3 block400S4

theorem block400RightChunk002ParamsCertificate_eq_true :
    block400RightChunk002ParamsCertificate = true := by
  native_decide

theorem block400_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block400RightChunk002L : ℝ) (block400RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block400S1 : ℝ))
    (hy2ne : y ≠ (block400S2 : ℝ))
    (hy3ne : y ≠ (block400S3 : ℝ))
    (hy4ne : y ≠ (block400S4 : ℝ)) :
    0 < block400V y := by
  have hcert := block400RightChunk002Certificate_eq_true
  unfold block400RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block400RightChunk002) (lo := block400RightChunk002L) (hi := block400RightChunk002R)
    (w1 := block400W1) (w2 := block400W2) (w3 := block400W3) (w4 := block400W4)
    (s1 := block400S1) (s2 := block400S2) (s3 := block400S3) (s4 := block400S4)
    hboxes hcover block400RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block400RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block400RightChunk003 block400W1 block400W2 block400W3 block400W4 block400S1 block400S2 block400S3 block400S4

theorem block400RightChunk003ParamsCertificate_eq_true :
    block400RightChunk003ParamsCertificate = true := by
  native_decide

theorem block400_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block400RightChunk003L : ℝ) (block400RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block400S1 : ℝ))
    (hy2ne : y ≠ (block400S2 : ℝ))
    (hy3ne : y ≠ (block400S3 : ℝ))
    (hy4ne : y ≠ (block400S4 : ℝ)) :
    0 < block400V y := by
  have hcert := block400RightChunk003Certificate_eq_true
  unfold block400RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block400RightChunk003) (lo := block400RightChunk003L) (hi := block400RightChunk003R)
    (w1 := block400W1) (w2 := block400W2) (w3 := block400W3) (w4 := block400W4)
    (s1 := block400S1) (s2 := block400S2) (s3 := block400S3) (s4 := block400S4)
    hboxes hcover block400RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block400_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block400RightL : ℝ) (block400RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block400S1 : ℝ))
    (hy2ne : y ≠ (block400S2 : ℝ))
    (hy3ne : y ≠ (block400S3 : ℝ))
    (hy4ne : y ≠ (block400S4 : ℝ)) :
    0 < block400V y := by
  by_cases h0 : y ≤ (block400RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block400RightChunk000L : ℝ) (block400RightChunk000R : ℝ) := by
      have hL : (block400RightChunk000L : ℝ) = (block400RightL : ℝ) := by
        norm_num [block400RightChunk000L, block400RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block400_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block400RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block400RightChunk001L : ℝ) (block400RightChunk001R : ℝ) := by
        have hprev : (block400RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block400RightChunk001L : ℝ) = (block400RightChunk000R : ℝ) := by
          norm_num [block400RightChunk001L, block400RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block400_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block400RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block400RightChunk002L : ℝ) (block400RightChunk002R : ℝ) := by
          have hprev : (block400RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block400RightChunk002L : ℝ) = (block400RightChunk001R : ℝ) := by
            norm_num [block400RightChunk002L, block400RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block400_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block400RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block400RightChunk003L : ℝ) = (block400RightChunk002R : ℝ) := by
          norm_num [block400RightChunk003L, block400RightChunk002R]
        have hR : (block400RightChunk003R : ℝ) = (block400RightR : ℝ) := by
          norm_num [block400RightChunk003R, block400RightR]
        have hyc : y ∈ Icc (block400RightChunk003L : ℝ) (block400RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block400_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block400_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block400LeftL : ℝ) (block400LeftR : ℝ) →
    y ≠ 0 → y ≠ (block400S1 : ℝ) → y ≠ (block400S2 : ℝ) →
    y ≠ (block400S3 : ℝ) → y ≠ (block400S4 : ℝ) → 0 < block400V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block400RightL : ℝ) (block400RightR : ℝ) →
    y ≠ 0 → y ≠ (block400S1 : ℝ) → y ≠ (block400S2 : ℝ) →
    y ≠ (block400S3 : ℝ) → y ≠ (block400S4 : ℝ) → 0 < block400V y)

theorem block400_reallog_certificate_proof :
    block400_reallog_certificate := by
  exact ⟨block400_left_V_pos, block400_right_V_pos⟩

end Block400
end M1817475
end Erdos1038Lean
