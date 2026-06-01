import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block225

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block225

open Set

def block225W1 : Rat := ((2392046568589277 : Rat) / 2500000000000000)
def block225W2 : Rat := ((28024047631773203 : Rat) / 500000000000000000)
def block225W3 : Rat := ((17137840914587033 : Rat) / 100000000000000000)
def block225W4 : Rat := ((4963071716629191 : Rat) / 50000000000000000)
def block225S1 : Rat := ((18174751 : Rat) / 10000000)
def block225S2 : Rat := ((511587 : Rat) / 200000)
def block225S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block225S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block225V (y : ℝ) : ℝ :=
  ratPotential block225W1 block225W2 block225W3 block225W4 block225S1 block225S2 block225S3 block225S4 y

def block225LeftParamsCertificate : Bool :=
  allBoxesSameParams block225LeftBoxes block225W1 block225W2 block225W3 block225W4 block225S1 block225S2 block225S3 block225S4

theorem block225LeftParamsCertificate_eq_true :
    block225LeftParamsCertificate = true := by
  native_decide

theorem block225_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block225LeftL : ℝ) (block225LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block225S1 : ℝ))
    (hy2ne : y ≠ (block225S2 : ℝ))
    (hy3ne : y ≠ (block225S3 : ℝ))
    (hy4ne : y ≠ (block225S4 : ℝ)) :
    0 < block225V y := by
  have hcert := block225LeftCertificate_eq_true
  unfold block225LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block225LeftBoxes) (lo := block225LeftL) (hi := block225LeftR)
    (w1 := block225W1) (w2 := block225W2) (w3 := block225W3) (w4 := block225W4)
    (s1 := block225S1) (s2 := block225S2) (s3 := block225S3) (s4 := block225S4)
    hboxes hcover block225LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block225RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block225RightChunk000 block225W1 block225W2 block225W3 block225W4 block225S1 block225S2 block225S3 block225S4

theorem block225RightChunk000ParamsCertificate_eq_true :
    block225RightChunk000ParamsCertificate = true := by
  native_decide

theorem block225_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block225RightChunk000L : ℝ) (block225RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block225S1 : ℝ))
    (hy2ne : y ≠ (block225S2 : ℝ))
    (hy3ne : y ≠ (block225S3 : ℝ))
    (hy4ne : y ≠ (block225S4 : ℝ)) :
    0 < block225V y := by
  have hcert := block225RightChunk000Certificate_eq_true
  unfold block225RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block225RightChunk000) (lo := block225RightChunk000L) (hi := block225RightChunk000R)
    (w1 := block225W1) (w2 := block225W2) (w3 := block225W3) (w4 := block225W4)
    (s1 := block225S1) (s2 := block225S2) (s3 := block225S3) (s4 := block225S4)
    hboxes hcover block225RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block225RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block225RightChunk001 block225W1 block225W2 block225W3 block225W4 block225S1 block225S2 block225S3 block225S4

theorem block225RightChunk001ParamsCertificate_eq_true :
    block225RightChunk001ParamsCertificate = true := by
  native_decide

theorem block225_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block225RightChunk001L : ℝ) (block225RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block225S1 : ℝ))
    (hy2ne : y ≠ (block225S2 : ℝ))
    (hy3ne : y ≠ (block225S3 : ℝ))
    (hy4ne : y ≠ (block225S4 : ℝ)) :
    0 < block225V y := by
  have hcert := block225RightChunk001Certificate_eq_true
  unfold block225RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block225RightChunk001) (lo := block225RightChunk001L) (hi := block225RightChunk001R)
    (w1 := block225W1) (w2 := block225W2) (w3 := block225W3) (w4 := block225W4)
    (s1 := block225S1) (s2 := block225S2) (s3 := block225S3) (s4 := block225S4)
    hboxes hcover block225RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block225RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block225RightChunk002 block225W1 block225W2 block225W3 block225W4 block225S1 block225S2 block225S3 block225S4

theorem block225RightChunk002ParamsCertificate_eq_true :
    block225RightChunk002ParamsCertificate = true := by
  native_decide

theorem block225_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block225RightChunk002L : ℝ) (block225RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block225S1 : ℝ))
    (hy2ne : y ≠ (block225S2 : ℝ))
    (hy3ne : y ≠ (block225S3 : ℝ))
    (hy4ne : y ≠ (block225S4 : ℝ)) :
    0 < block225V y := by
  have hcert := block225RightChunk002Certificate_eq_true
  unfold block225RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block225RightChunk002) (lo := block225RightChunk002L) (hi := block225RightChunk002R)
    (w1 := block225W1) (w2 := block225W2) (w3 := block225W3) (w4 := block225W4)
    (s1 := block225S1) (s2 := block225S2) (s3 := block225S3) (s4 := block225S4)
    hboxes hcover block225RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block225_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block225RightL : ℝ) (block225RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block225S1 : ℝ))
    (hy2ne : y ≠ (block225S2 : ℝ))
    (hy3ne : y ≠ (block225S3 : ℝ))
    (hy4ne : y ≠ (block225S4 : ℝ)) :
    0 < block225V y := by
  by_cases h0 : y ≤ (block225RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block225RightChunk000L : ℝ) (block225RightChunk000R : ℝ) := by
      have hL : (block225RightChunk000L : ℝ) = (block225RightL : ℝ) := by
        norm_num [block225RightChunk000L, block225RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block225_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block225RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block225RightChunk001L : ℝ) (block225RightChunk001R : ℝ) := by
        have hprev : (block225RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block225RightChunk001L : ℝ) = (block225RightChunk000R : ℝ) := by
          norm_num [block225RightChunk001L, block225RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block225_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block225RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block225RightChunk002L : ℝ) = (block225RightChunk001R : ℝ) := by
        norm_num [block225RightChunk002L, block225RightChunk001R]
      have hR : (block225RightChunk002R : ℝ) = (block225RightR : ℝ) := by
        norm_num [block225RightChunk002R, block225RightR]
      have hyc : y ∈ Icc (block225RightChunk002L : ℝ) (block225RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block225_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block225_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block225LeftL : ℝ) (block225LeftR : ℝ) →
    y ≠ 0 → y ≠ (block225S1 : ℝ) → y ≠ (block225S2 : ℝ) →
    y ≠ (block225S3 : ℝ) → y ≠ (block225S4 : ℝ) → 0 < block225V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block225RightL : ℝ) (block225RightR : ℝ) →
    y ≠ 0 → y ≠ (block225S1 : ℝ) → y ≠ (block225S2 : ℝ) →
    y ≠ (block225S3 : ℝ) → y ≠ (block225S4 : ℝ) → 0 < block225V y)

theorem block225_reallog_certificate_proof :
    block225_reallog_certificate := by
  exact ⟨block225_left_V_pos, block225_right_V_pos⟩

end Block225
end M1817475
end Erdos1038Lean
