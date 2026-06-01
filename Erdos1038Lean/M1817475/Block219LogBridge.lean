import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block219

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block219

open Set

def block219W1 : Rat := ((9605999045739281 : Rat) / 10000000000000000)
def block219W2 : Rat := ((5484179584872373 : Rat) / 100000000000000000)
def block219W3 : Rat := ((17292494953694873 : Rat) / 100000000000000000)
def block219W4 : Rat := ((1970024129052757 : Rat) / 20000000000000000)
def block219S1 : Rat := ((18174751 : Rat) / 10000000)
def block219S2 : Rat := ((511587 : Rat) / 200000)
def block219S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block219S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block219V (y : ℝ) : ℝ :=
  ratPotential block219W1 block219W2 block219W3 block219W4 block219S1 block219S2 block219S3 block219S4 y

def block219LeftParamsCertificate : Bool :=
  allBoxesSameParams block219LeftBoxes block219W1 block219W2 block219W3 block219W4 block219S1 block219S2 block219S3 block219S4

theorem block219LeftParamsCertificate_eq_true :
    block219LeftParamsCertificate = true := by
  native_decide

theorem block219_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block219LeftL : ℝ) (block219LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block219S1 : ℝ))
    (hy2ne : y ≠ (block219S2 : ℝ))
    (hy3ne : y ≠ (block219S3 : ℝ))
    (hy4ne : y ≠ (block219S4 : ℝ)) :
    0 < block219V y := by
  have hcert := block219LeftCertificate_eq_true
  unfold block219LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block219LeftBoxes) (lo := block219LeftL) (hi := block219LeftR)
    (w1 := block219W1) (w2 := block219W2) (w3 := block219W3) (w4 := block219W4)
    (s1 := block219S1) (s2 := block219S2) (s3 := block219S3) (s4 := block219S4)
    hboxes hcover block219LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block219RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block219RightChunk000 block219W1 block219W2 block219W3 block219W4 block219S1 block219S2 block219S3 block219S4

theorem block219RightChunk000ParamsCertificate_eq_true :
    block219RightChunk000ParamsCertificate = true := by
  native_decide

theorem block219_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block219RightChunk000L : ℝ) (block219RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block219S1 : ℝ))
    (hy2ne : y ≠ (block219S2 : ℝ))
    (hy3ne : y ≠ (block219S3 : ℝ))
    (hy4ne : y ≠ (block219S4 : ℝ)) :
    0 < block219V y := by
  have hcert := block219RightChunk000Certificate_eq_true
  unfold block219RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block219RightChunk000) (lo := block219RightChunk000L) (hi := block219RightChunk000R)
    (w1 := block219W1) (w2 := block219W2) (w3 := block219W3) (w4 := block219W4)
    (s1 := block219S1) (s2 := block219S2) (s3 := block219S3) (s4 := block219S4)
    hboxes hcover block219RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block219RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block219RightChunk001 block219W1 block219W2 block219W3 block219W4 block219S1 block219S2 block219S3 block219S4

theorem block219RightChunk001ParamsCertificate_eq_true :
    block219RightChunk001ParamsCertificate = true := by
  native_decide

theorem block219_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block219RightChunk001L : ℝ) (block219RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block219S1 : ℝ))
    (hy2ne : y ≠ (block219S2 : ℝ))
    (hy3ne : y ≠ (block219S3 : ℝ))
    (hy4ne : y ≠ (block219S4 : ℝ)) :
    0 < block219V y := by
  have hcert := block219RightChunk001Certificate_eq_true
  unfold block219RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block219RightChunk001) (lo := block219RightChunk001L) (hi := block219RightChunk001R)
    (w1 := block219W1) (w2 := block219W2) (w3 := block219W3) (w4 := block219W4)
    (s1 := block219S1) (s2 := block219S2) (s3 := block219S3) (s4 := block219S4)
    hboxes hcover block219RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block219RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block219RightChunk002 block219W1 block219W2 block219W3 block219W4 block219S1 block219S2 block219S3 block219S4

theorem block219RightChunk002ParamsCertificate_eq_true :
    block219RightChunk002ParamsCertificate = true := by
  native_decide

theorem block219_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block219RightChunk002L : ℝ) (block219RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block219S1 : ℝ))
    (hy2ne : y ≠ (block219S2 : ℝ))
    (hy3ne : y ≠ (block219S3 : ℝ))
    (hy4ne : y ≠ (block219S4 : ℝ)) :
    0 < block219V y := by
  have hcert := block219RightChunk002Certificate_eq_true
  unfold block219RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block219RightChunk002) (lo := block219RightChunk002L) (hi := block219RightChunk002R)
    (w1 := block219W1) (w2 := block219W2) (w3 := block219W3) (w4 := block219W4)
    (s1 := block219S1) (s2 := block219S2) (s3 := block219S3) (s4 := block219S4)
    hboxes hcover block219RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block219_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block219RightL : ℝ) (block219RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block219S1 : ℝ))
    (hy2ne : y ≠ (block219S2 : ℝ))
    (hy3ne : y ≠ (block219S3 : ℝ))
    (hy4ne : y ≠ (block219S4 : ℝ)) :
    0 < block219V y := by
  by_cases h0 : y ≤ (block219RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block219RightChunk000L : ℝ) (block219RightChunk000R : ℝ) := by
      have hL : (block219RightChunk000L : ℝ) = (block219RightL : ℝ) := by
        norm_num [block219RightChunk000L, block219RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block219_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block219RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block219RightChunk001L : ℝ) (block219RightChunk001R : ℝ) := by
        have hprev : (block219RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block219RightChunk001L : ℝ) = (block219RightChunk000R : ℝ) := by
          norm_num [block219RightChunk001L, block219RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block219_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block219RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block219RightChunk002L : ℝ) = (block219RightChunk001R : ℝ) := by
        norm_num [block219RightChunk002L, block219RightChunk001R]
      have hR : (block219RightChunk002R : ℝ) = (block219RightR : ℝ) := by
        norm_num [block219RightChunk002R, block219RightR]
      have hyc : y ∈ Icc (block219RightChunk002L : ℝ) (block219RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block219_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block219_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block219LeftL : ℝ) (block219LeftR : ℝ) →
    y ≠ 0 → y ≠ (block219S1 : ℝ) → y ≠ (block219S2 : ℝ) →
    y ≠ (block219S3 : ℝ) → y ≠ (block219S4 : ℝ) → 0 < block219V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block219RightL : ℝ) (block219RightR : ℝ) →
    y ≠ 0 → y ≠ (block219S1 : ℝ) → y ≠ (block219S2 : ℝ) →
    y ≠ (block219S3 : ℝ) → y ≠ (block219S4 : ℝ) → 0 < block219V y)

theorem block219_reallog_certificate_proof :
    block219_reallog_certificate := by
  exact ⟨block219_left_V_pos, block219_right_V_pos⟩

end Block219
end M1817475
end Erdos1038Lean
