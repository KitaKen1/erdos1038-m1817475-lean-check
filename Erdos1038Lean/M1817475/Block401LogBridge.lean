import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block401

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block401

open Set

def block401W1 : Rat := ((7475500865916797 : Rat) / 10000000000000000)
def block401W2 : Rat := (0 : Rat)
def block401W3 : Rat := ((27738979215141 : Rat) / 100000000000000)
def block401W4 : Rat := ((4664621910007113 : Rat) / 50000000000000000)
def block401S1 : Rat := ((18174751 : Rat) / 10000000)
def block401S2 : Rat := ((511587 : Rat) / 200000)
def block401S3 : Rat := ((132294365267857142921 : Rat) / 50000000000000000000)
def block401S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block401V (y : ℝ) : ℝ :=
  ratPotential block401W1 block401W2 block401W3 block401W4 block401S1 block401S2 block401S3 block401S4 y

def block401LeftParamsCertificate : Bool :=
  allBoxesSameParams block401LeftBoxes block401W1 block401W2 block401W3 block401W4 block401S1 block401S2 block401S3 block401S4

theorem block401LeftParamsCertificate_eq_true :
    block401LeftParamsCertificate = true := by
  native_decide

theorem block401_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block401LeftL : ℝ) (block401LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block401S1 : ℝ))
    (hy2ne : y ≠ (block401S2 : ℝ))
    (hy3ne : y ≠ (block401S3 : ℝ))
    (hy4ne : y ≠ (block401S4 : ℝ)) :
    0 < block401V y := by
  have hcert := block401LeftCertificate_eq_true
  unfold block401LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block401LeftBoxes) (lo := block401LeftL) (hi := block401LeftR)
    (w1 := block401W1) (w2 := block401W2) (w3 := block401W3) (w4 := block401W4)
    (s1 := block401S1) (s2 := block401S2) (s3 := block401S3) (s4 := block401S4)
    hboxes hcover block401LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block401RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block401RightChunk000 block401W1 block401W2 block401W3 block401W4 block401S1 block401S2 block401S3 block401S4

theorem block401RightChunk000ParamsCertificate_eq_true :
    block401RightChunk000ParamsCertificate = true := by
  native_decide

theorem block401_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block401RightChunk000L : ℝ) (block401RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block401S1 : ℝ))
    (hy2ne : y ≠ (block401S2 : ℝ))
    (hy3ne : y ≠ (block401S3 : ℝ))
    (hy4ne : y ≠ (block401S4 : ℝ)) :
    0 < block401V y := by
  have hcert := block401RightChunk000Certificate_eq_true
  unfold block401RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block401RightChunk000) (lo := block401RightChunk000L) (hi := block401RightChunk000R)
    (w1 := block401W1) (w2 := block401W2) (w3 := block401W3) (w4 := block401W4)
    (s1 := block401S1) (s2 := block401S2) (s3 := block401S3) (s4 := block401S4)
    hboxes hcover block401RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block401RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block401RightChunk001 block401W1 block401W2 block401W3 block401W4 block401S1 block401S2 block401S3 block401S4

theorem block401RightChunk001ParamsCertificate_eq_true :
    block401RightChunk001ParamsCertificate = true := by
  native_decide

theorem block401_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block401RightChunk001L : ℝ) (block401RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block401S1 : ℝ))
    (hy2ne : y ≠ (block401S2 : ℝ))
    (hy3ne : y ≠ (block401S3 : ℝ))
    (hy4ne : y ≠ (block401S4 : ℝ)) :
    0 < block401V y := by
  have hcert := block401RightChunk001Certificate_eq_true
  unfold block401RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block401RightChunk001) (lo := block401RightChunk001L) (hi := block401RightChunk001R)
    (w1 := block401W1) (w2 := block401W2) (w3 := block401W3) (w4 := block401W4)
    (s1 := block401S1) (s2 := block401S2) (s3 := block401S3) (s4 := block401S4)
    hboxes hcover block401RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block401RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block401RightChunk002 block401W1 block401W2 block401W3 block401W4 block401S1 block401S2 block401S3 block401S4

theorem block401RightChunk002ParamsCertificate_eq_true :
    block401RightChunk002ParamsCertificate = true := by
  native_decide

theorem block401_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block401RightChunk002L : ℝ) (block401RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block401S1 : ℝ))
    (hy2ne : y ≠ (block401S2 : ℝ))
    (hy3ne : y ≠ (block401S3 : ℝ))
    (hy4ne : y ≠ (block401S4 : ℝ)) :
    0 < block401V y := by
  have hcert := block401RightChunk002Certificate_eq_true
  unfold block401RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block401RightChunk002) (lo := block401RightChunk002L) (hi := block401RightChunk002R)
    (w1 := block401W1) (w2 := block401W2) (w3 := block401W3) (w4 := block401W4)
    (s1 := block401S1) (s2 := block401S2) (s3 := block401S3) (s4 := block401S4)
    hboxes hcover block401RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block401RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block401RightChunk003 block401W1 block401W2 block401W3 block401W4 block401S1 block401S2 block401S3 block401S4

theorem block401RightChunk003ParamsCertificate_eq_true :
    block401RightChunk003ParamsCertificate = true := by
  native_decide

theorem block401_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block401RightChunk003L : ℝ) (block401RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block401S1 : ℝ))
    (hy2ne : y ≠ (block401S2 : ℝ))
    (hy3ne : y ≠ (block401S3 : ℝ))
    (hy4ne : y ≠ (block401S4 : ℝ)) :
    0 < block401V y := by
  have hcert := block401RightChunk003Certificate_eq_true
  unfold block401RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block401RightChunk003) (lo := block401RightChunk003L) (hi := block401RightChunk003R)
    (w1 := block401W1) (w2 := block401W2) (w3 := block401W3) (w4 := block401W4)
    (s1 := block401S1) (s2 := block401S2) (s3 := block401S3) (s4 := block401S4)
    hboxes hcover block401RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block401_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block401RightL : ℝ) (block401RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block401S1 : ℝ))
    (hy2ne : y ≠ (block401S2 : ℝ))
    (hy3ne : y ≠ (block401S3 : ℝ))
    (hy4ne : y ≠ (block401S4 : ℝ)) :
    0 < block401V y := by
  by_cases h0 : y ≤ (block401RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block401RightChunk000L : ℝ) (block401RightChunk000R : ℝ) := by
      have hL : (block401RightChunk000L : ℝ) = (block401RightL : ℝ) := by
        norm_num [block401RightChunk000L, block401RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block401_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block401RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block401RightChunk001L : ℝ) (block401RightChunk001R : ℝ) := by
        have hprev : (block401RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block401RightChunk001L : ℝ) = (block401RightChunk000R : ℝ) := by
          norm_num [block401RightChunk001L, block401RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block401_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block401RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block401RightChunk002L : ℝ) (block401RightChunk002R : ℝ) := by
          have hprev : (block401RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block401RightChunk002L : ℝ) = (block401RightChunk001R : ℝ) := by
            norm_num [block401RightChunk002L, block401RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block401_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block401RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block401RightChunk003L : ℝ) = (block401RightChunk002R : ℝ) := by
          norm_num [block401RightChunk003L, block401RightChunk002R]
        have hR : (block401RightChunk003R : ℝ) = (block401RightR : ℝ) := by
          norm_num [block401RightChunk003R, block401RightR]
        have hyc : y ∈ Icc (block401RightChunk003L : ℝ) (block401RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block401_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block401_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block401LeftL : ℝ) (block401LeftR : ℝ) →
    y ≠ 0 → y ≠ (block401S1 : ℝ) → y ≠ (block401S2 : ℝ) →
    y ≠ (block401S3 : ℝ) → y ≠ (block401S4 : ℝ) → 0 < block401V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block401RightL : ℝ) (block401RightR : ℝ) →
    y ≠ 0 → y ≠ (block401S1 : ℝ) → y ≠ (block401S2 : ℝ) →
    y ≠ (block401S3 : ℝ) → y ≠ (block401S4 : ℝ) → 0 < block401V y)

theorem block401_reallog_certificate_proof :
    block401_reallog_certificate := by
  exact ⟨block401_left_V_pos, block401_right_V_pos⟩

end Block401
end M1817475
end Erdos1038Lean
