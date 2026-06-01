import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block218

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block218

open Set

def block218W1 : Rat := ((9611782117313793 : Rat) / 10000000000000000)
def block218W2 : Rat := ((10931420990365577 : Rat) / 200000000000000000)
def block218W3 : Rat := ((1731618839431709 : Rat) / 10000000000000000)
def block218W4 : Rat := ((9838448564611717 : Rat) / 100000000000000000)
def block218S1 : Rat := ((18174751 : Rat) / 10000000)
def block218S2 : Rat := ((511587 : Rat) / 200000)
def block218S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block218S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block218V (y : ℝ) : ℝ :=
  ratPotential block218W1 block218W2 block218W3 block218W4 block218S1 block218S2 block218S3 block218S4 y

def block218LeftParamsCertificate : Bool :=
  allBoxesSameParams block218LeftBoxes block218W1 block218W2 block218W3 block218W4 block218S1 block218S2 block218S3 block218S4

theorem block218LeftParamsCertificate_eq_true :
    block218LeftParamsCertificate = true := by
  native_decide

theorem block218_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block218LeftL : ℝ) (block218LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block218S1 : ℝ))
    (hy2ne : y ≠ (block218S2 : ℝ))
    (hy3ne : y ≠ (block218S3 : ℝ))
    (hy4ne : y ≠ (block218S4 : ℝ)) :
    0 < block218V y := by
  have hcert := block218LeftCertificate_eq_true
  unfold block218LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block218LeftBoxes) (lo := block218LeftL) (hi := block218LeftR)
    (w1 := block218W1) (w2 := block218W2) (w3 := block218W3) (w4 := block218W4)
    (s1 := block218S1) (s2 := block218S2) (s3 := block218S3) (s4 := block218S4)
    hboxes hcover block218LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block218RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block218RightChunk000 block218W1 block218W2 block218W3 block218W4 block218S1 block218S2 block218S3 block218S4

theorem block218RightChunk000ParamsCertificate_eq_true :
    block218RightChunk000ParamsCertificate = true := by
  native_decide

theorem block218_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block218RightChunk000L : ℝ) (block218RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block218S1 : ℝ))
    (hy2ne : y ≠ (block218S2 : ℝ))
    (hy3ne : y ≠ (block218S3 : ℝ))
    (hy4ne : y ≠ (block218S4 : ℝ)) :
    0 < block218V y := by
  have hcert := block218RightChunk000Certificate_eq_true
  unfold block218RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block218RightChunk000) (lo := block218RightChunk000L) (hi := block218RightChunk000R)
    (w1 := block218W1) (w2 := block218W2) (w3 := block218W3) (w4 := block218W4)
    (s1 := block218S1) (s2 := block218S2) (s3 := block218S3) (s4 := block218S4)
    hboxes hcover block218RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block218RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block218RightChunk001 block218W1 block218W2 block218W3 block218W4 block218S1 block218S2 block218S3 block218S4

theorem block218RightChunk001ParamsCertificate_eq_true :
    block218RightChunk001ParamsCertificate = true := by
  native_decide

theorem block218_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block218RightChunk001L : ℝ) (block218RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block218S1 : ℝ))
    (hy2ne : y ≠ (block218S2 : ℝ))
    (hy3ne : y ≠ (block218S3 : ℝ))
    (hy4ne : y ≠ (block218S4 : ℝ)) :
    0 < block218V y := by
  have hcert := block218RightChunk001Certificate_eq_true
  unfold block218RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block218RightChunk001) (lo := block218RightChunk001L) (hi := block218RightChunk001R)
    (w1 := block218W1) (w2 := block218W2) (w3 := block218W3) (w4 := block218W4)
    (s1 := block218S1) (s2 := block218S2) (s3 := block218S3) (s4 := block218S4)
    hboxes hcover block218RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block218RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block218RightChunk002 block218W1 block218W2 block218W3 block218W4 block218S1 block218S2 block218S3 block218S4

theorem block218RightChunk002ParamsCertificate_eq_true :
    block218RightChunk002ParamsCertificate = true := by
  native_decide

theorem block218_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block218RightChunk002L : ℝ) (block218RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block218S1 : ℝ))
    (hy2ne : y ≠ (block218S2 : ℝ))
    (hy3ne : y ≠ (block218S3 : ℝ))
    (hy4ne : y ≠ (block218S4 : ℝ)) :
    0 < block218V y := by
  have hcert := block218RightChunk002Certificate_eq_true
  unfold block218RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block218RightChunk002) (lo := block218RightChunk002L) (hi := block218RightChunk002R)
    (w1 := block218W1) (w2 := block218W2) (w3 := block218W3) (w4 := block218W4)
    (s1 := block218S1) (s2 := block218S2) (s3 := block218S3) (s4 := block218S4)
    hboxes hcover block218RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block218_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block218RightL : ℝ) (block218RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block218S1 : ℝ))
    (hy2ne : y ≠ (block218S2 : ℝ))
    (hy3ne : y ≠ (block218S3 : ℝ))
    (hy4ne : y ≠ (block218S4 : ℝ)) :
    0 < block218V y := by
  by_cases h0 : y ≤ (block218RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block218RightChunk000L : ℝ) (block218RightChunk000R : ℝ) := by
      have hL : (block218RightChunk000L : ℝ) = (block218RightL : ℝ) := by
        norm_num [block218RightChunk000L, block218RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block218_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block218RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block218RightChunk001L : ℝ) (block218RightChunk001R : ℝ) := by
        have hprev : (block218RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block218RightChunk001L : ℝ) = (block218RightChunk000R : ℝ) := by
          norm_num [block218RightChunk001L, block218RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block218_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block218RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block218RightChunk002L : ℝ) = (block218RightChunk001R : ℝ) := by
        norm_num [block218RightChunk002L, block218RightChunk001R]
      have hR : (block218RightChunk002R : ℝ) = (block218RightR : ℝ) := by
        norm_num [block218RightChunk002R, block218RightR]
      have hyc : y ∈ Icc (block218RightChunk002L : ℝ) (block218RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block218_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block218_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block218LeftL : ℝ) (block218LeftR : ℝ) →
    y ≠ 0 → y ≠ (block218S1 : ℝ) → y ≠ (block218S2 : ℝ) →
    y ≠ (block218S3 : ℝ) → y ≠ (block218S4 : ℝ) → 0 < block218V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block218RightL : ℝ) (block218RightR : ℝ) →
    y ≠ 0 → y ≠ (block218S1 : ℝ) → y ≠ (block218S2 : ℝ) →
    y ≠ (block218S3 : ℝ) → y ≠ (block218S4 : ℝ) → 0 < block218V y)

theorem block218_reallog_certificate_proof :
    block218_reallog_certificate := by
  exact ⟨block218_left_V_pos, block218_right_V_pos⟩

end Block218
end M1817475
end Erdos1038Lean
