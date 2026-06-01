import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block191

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block191

open Set

def block191W1 : Rat := ((8742270703664793 : Rat) / 5000000000000000)
def block191W2 : Rat := (0 : Rat)
def block191W3 : Rat := ((45021711206961 : Rat) / 250000000000000)
def block191W4 : Rat := ((9245539747691897 : Rat) / 100000000000000000)
def block191S1 : Rat := ((18174751 : Rat) / 10000000)
def block191S2 : Rat := ((511587 : Rat) / 200000)
def block191S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block191S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block191V (y : ℝ) : ℝ :=
  ratPotential block191W1 block191W2 block191W3 block191W4 block191S1 block191S2 block191S3 block191S4 y

def block191LeftParamsCertificate : Bool :=
  allBoxesSameParams block191LeftBoxes block191W1 block191W2 block191W3 block191W4 block191S1 block191S2 block191S3 block191S4

theorem block191LeftParamsCertificate_eq_true :
    block191LeftParamsCertificate = true := by
  native_decide

theorem block191_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block191LeftL : ℝ) (block191LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block191S1 : ℝ))
    (hy2ne : y ≠ (block191S2 : ℝ))
    (hy3ne : y ≠ (block191S3 : ℝ))
    (hy4ne : y ≠ (block191S4 : ℝ)) :
    0 < block191V y := by
  have hcert := block191LeftCertificate_eq_true
  unfold block191LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block191LeftBoxes) (lo := block191LeftL) (hi := block191LeftR)
    (w1 := block191W1) (w2 := block191W2) (w3 := block191W3) (w4 := block191W4)
    (s1 := block191S1) (s2 := block191S2) (s3 := block191S3) (s4 := block191S4)
    hboxes hcover block191LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block191RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block191RightChunk000 block191W1 block191W2 block191W3 block191W4 block191S1 block191S2 block191S3 block191S4

theorem block191RightChunk000ParamsCertificate_eq_true :
    block191RightChunk000ParamsCertificate = true := by
  native_decide

theorem block191_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block191RightChunk000L : ℝ) (block191RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block191S1 : ℝ))
    (hy2ne : y ≠ (block191S2 : ℝ))
    (hy3ne : y ≠ (block191S3 : ℝ))
    (hy4ne : y ≠ (block191S4 : ℝ)) :
    0 < block191V y := by
  have hcert := block191RightChunk000Certificate_eq_true
  unfold block191RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block191RightChunk000) (lo := block191RightChunk000L) (hi := block191RightChunk000R)
    (w1 := block191W1) (w2 := block191W2) (w3 := block191W3) (w4 := block191W4)
    (s1 := block191S1) (s2 := block191S2) (s3 := block191S3) (s4 := block191S4)
    hboxes hcover block191RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block191RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block191RightChunk001 block191W1 block191W2 block191W3 block191W4 block191S1 block191S2 block191S3 block191S4

theorem block191RightChunk001ParamsCertificate_eq_true :
    block191RightChunk001ParamsCertificate = true := by
  native_decide

theorem block191_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block191RightChunk001L : ℝ) (block191RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block191S1 : ℝ))
    (hy2ne : y ≠ (block191S2 : ℝ))
    (hy3ne : y ≠ (block191S3 : ℝ))
    (hy4ne : y ≠ (block191S4 : ℝ)) :
    0 < block191V y := by
  have hcert := block191RightChunk001Certificate_eq_true
  unfold block191RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block191RightChunk001) (lo := block191RightChunk001L) (hi := block191RightChunk001R)
    (w1 := block191W1) (w2 := block191W2) (w3 := block191W3) (w4 := block191W4)
    (s1 := block191S1) (s2 := block191S2) (s3 := block191S3) (s4 := block191S4)
    hboxes hcover block191RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block191RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block191RightChunk002 block191W1 block191W2 block191W3 block191W4 block191S1 block191S2 block191S3 block191S4

theorem block191RightChunk002ParamsCertificate_eq_true :
    block191RightChunk002ParamsCertificate = true := by
  native_decide

theorem block191_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block191RightChunk002L : ℝ) (block191RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block191S1 : ℝ))
    (hy2ne : y ≠ (block191S2 : ℝ))
    (hy3ne : y ≠ (block191S3 : ℝ))
    (hy4ne : y ≠ (block191S4 : ℝ)) :
    0 < block191V y := by
  have hcert := block191RightChunk002Certificate_eq_true
  unfold block191RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block191RightChunk002) (lo := block191RightChunk002L) (hi := block191RightChunk002R)
    (w1 := block191W1) (w2 := block191W2) (w3 := block191W3) (w4 := block191W4)
    (s1 := block191S1) (s2 := block191S2) (s3 := block191S3) (s4 := block191S4)
    hboxes hcover block191RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block191_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block191RightL : ℝ) (block191RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block191S1 : ℝ))
    (hy2ne : y ≠ (block191S2 : ℝ))
    (hy3ne : y ≠ (block191S3 : ℝ))
    (hy4ne : y ≠ (block191S4 : ℝ)) :
    0 < block191V y := by
  by_cases h0 : y ≤ (block191RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block191RightChunk000L : ℝ) (block191RightChunk000R : ℝ) := by
      have hL : (block191RightChunk000L : ℝ) = (block191RightL : ℝ) := by
        norm_num [block191RightChunk000L, block191RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block191_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block191RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block191RightChunk001L : ℝ) (block191RightChunk001R : ℝ) := by
        have hprev : (block191RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block191RightChunk001L : ℝ) = (block191RightChunk000R : ℝ) := by
          norm_num [block191RightChunk001L, block191RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block191_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block191RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block191RightChunk002L : ℝ) = (block191RightChunk001R : ℝ) := by
        norm_num [block191RightChunk002L, block191RightChunk001R]
      have hR : (block191RightChunk002R : ℝ) = (block191RightR : ℝ) := by
        norm_num [block191RightChunk002R, block191RightR]
      have hyc : y ∈ Icc (block191RightChunk002L : ℝ) (block191RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block191_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block191_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block191LeftL : ℝ) (block191LeftR : ℝ) →
    y ≠ 0 → y ≠ (block191S1 : ℝ) → y ≠ (block191S2 : ℝ) →
    y ≠ (block191S3 : ℝ) → y ≠ (block191S4 : ℝ) → 0 < block191V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block191RightL : ℝ) (block191RightR : ℝ) →
    y ≠ 0 → y ≠ (block191S1 : ℝ) → y ≠ (block191S2 : ℝ) →
    y ≠ (block191S3 : ℝ) → y ≠ (block191S4 : ℝ) → 0 < block191V y)

theorem block191_reallog_certificate_proof :
    block191_reallog_certificate := by
  exact ⟨block191_left_V_pos, block191_right_V_pos⟩

end Block191
end M1817475
end Erdos1038Lean
