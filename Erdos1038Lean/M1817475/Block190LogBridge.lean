import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block190

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block190

open Set

def block190W1 : Rat := ((4380723730492841 : Rat) / 2500000000000000)
def block190W2 : Rat := (0 : Rat)
def block190W3 : Rat := ((8971614818956307 : Rat) / 50000000000000000)
def block190W4 : Rat := ((9290765099386651 : Rat) / 100000000000000000)
def block190S1 : Rat := ((18174751 : Rat) / 10000000)
def block190S2 : Rat := ((511587 : Rat) / 200000)
def block190S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block190S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block190V (y : ℝ) : ℝ :=
  ratPotential block190W1 block190W2 block190W3 block190W4 block190S1 block190S2 block190S3 block190S4 y

def block190LeftParamsCertificate : Bool :=
  allBoxesSameParams block190LeftBoxes block190W1 block190W2 block190W3 block190W4 block190S1 block190S2 block190S3 block190S4

theorem block190LeftParamsCertificate_eq_true :
    block190LeftParamsCertificate = true := by
  native_decide

theorem block190_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block190LeftL : ℝ) (block190LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block190S1 : ℝ))
    (hy2ne : y ≠ (block190S2 : ℝ))
    (hy3ne : y ≠ (block190S3 : ℝ))
    (hy4ne : y ≠ (block190S4 : ℝ)) :
    0 < block190V y := by
  have hcert := block190LeftCertificate_eq_true
  unfold block190LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block190LeftBoxes) (lo := block190LeftL) (hi := block190LeftR)
    (w1 := block190W1) (w2 := block190W2) (w3 := block190W3) (w4 := block190W4)
    (s1 := block190S1) (s2 := block190S2) (s3 := block190S3) (s4 := block190S4)
    hboxes hcover block190LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block190RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block190RightChunk000 block190W1 block190W2 block190W3 block190W4 block190S1 block190S2 block190S3 block190S4

theorem block190RightChunk000ParamsCertificate_eq_true :
    block190RightChunk000ParamsCertificate = true := by
  native_decide

theorem block190_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block190RightChunk000L : ℝ) (block190RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block190S1 : ℝ))
    (hy2ne : y ≠ (block190S2 : ℝ))
    (hy3ne : y ≠ (block190S3 : ℝ))
    (hy4ne : y ≠ (block190S4 : ℝ)) :
    0 < block190V y := by
  have hcert := block190RightChunk000Certificate_eq_true
  unfold block190RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block190RightChunk000) (lo := block190RightChunk000L) (hi := block190RightChunk000R)
    (w1 := block190W1) (w2 := block190W2) (w3 := block190W3) (w4 := block190W4)
    (s1 := block190S1) (s2 := block190S2) (s3 := block190S3) (s4 := block190S4)
    hboxes hcover block190RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block190RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block190RightChunk001 block190W1 block190W2 block190W3 block190W4 block190S1 block190S2 block190S3 block190S4

theorem block190RightChunk001ParamsCertificate_eq_true :
    block190RightChunk001ParamsCertificate = true := by
  native_decide

theorem block190_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block190RightChunk001L : ℝ) (block190RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block190S1 : ℝ))
    (hy2ne : y ≠ (block190S2 : ℝ))
    (hy3ne : y ≠ (block190S3 : ℝ))
    (hy4ne : y ≠ (block190S4 : ℝ)) :
    0 < block190V y := by
  have hcert := block190RightChunk001Certificate_eq_true
  unfold block190RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block190RightChunk001) (lo := block190RightChunk001L) (hi := block190RightChunk001R)
    (w1 := block190W1) (w2 := block190W2) (w3 := block190W3) (w4 := block190W4)
    (s1 := block190S1) (s2 := block190S2) (s3 := block190S3) (s4 := block190S4)
    hboxes hcover block190RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block190RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block190RightChunk002 block190W1 block190W2 block190W3 block190W4 block190S1 block190S2 block190S3 block190S4

theorem block190RightChunk002ParamsCertificate_eq_true :
    block190RightChunk002ParamsCertificate = true := by
  native_decide

theorem block190_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block190RightChunk002L : ℝ) (block190RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block190S1 : ℝ))
    (hy2ne : y ≠ (block190S2 : ℝ))
    (hy3ne : y ≠ (block190S3 : ℝ))
    (hy4ne : y ≠ (block190S4 : ℝ)) :
    0 < block190V y := by
  have hcert := block190RightChunk002Certificate_eq_true
  unfold block190RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block190RightChunk002) (lo := block190RightChunk002L) (hi := block190RightChunk002R)
    (w1 := block190W1) (w2 := block190W2) (w3 := block190W3) (w4 := block190W4)
    (s1 := block190S1) (s2 := block190S2) (s3 := block190S3) (s4 := block190S4)
    hboxes hcover block190RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block190_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block190RightL : ℝ) (block190RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block190S1 : ℝ))
    (hy2ne : y ≠ (block190S2 : ℝ))
    (hy3ne : y ≠ (block190S3 : ℝ))
    (hy4ne : y ≠ (block190S4 : ℝ)) :
    0 < block190V y := by
  by_cases h0 : y ≤ (block190RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block190RightChunk000L : ℝ) (block190RightChunk000R : ℝ) := by
      have hL : (block190RightChunk000L : ℝ) = (block190RightL : ℝ) := by
        norm_num [block190RightChunk000L, block190RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block190_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block190RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block190RightChunk001L : ℝ) (block190RightChunk001R : ℝ) := by
        have hprev : (block190RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block190RightChunk001L : ℝ) = (block190RightChunk000R : ℝ) := by
          norm_num [block190RightChunk001L, block190RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block190_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block190RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block190RightChunk002L : ℝ) = (block190RightChunk001R : ℝ) := by
        norm_num [block190RightChunk002L, block190RightChunk001R]
      have hR : (block190RightChunk002R : ℝ) = (block190RightR : ℝ) := by
        norm_num [block190RightChunk002R, block190RightR]
      have hyc : y ∈ Icc (block190RightChunk002L : ℝ) (block190RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block190_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block190_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block190LeftL : ℝ) (block190LeftR : ℝ) →
    y ≠ 0 → y ≠ (block190S1 : ℝ) → y ≠ (block190S2 : ℝ) →
    y ≠ (block190S3 : ℝ) → y ≠ (block190S4 : ℝ) → 0 < block190V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block190RightL : ℝ) (block190RightR : ℝ) →
    y ≠ 0 → y ≠ (block190S1 : ℝ) → y ≠ (block190S2 : ℝ) →
    y ≠ (block190S3 : ℝ) → y ≠ (block190S4 : ℝ) → 0 < block190V y)

theorem block190_reallog_certificate_proof :
    block190_reallog_certificate := by
  exact ⟨block190_left_V_pos, block190_right_V_pos⟩

end Block190
end M1817475
end Erdos1038Lean
