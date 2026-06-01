import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block226

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block226

open Set

def block226W1 : Rat := ((4780411202199 : Rat) / 5000000000000)
def block226W2 : Rat := ((703522785695653 : Rat) / 12500000000000000)
def block226W3 : Rat := ((342156995406429 : Rat) / 2000000000000000)
def block226W4 : Rat := ((2485205481228077 : Rat) / 25000000000000000)
def block226S1 : Rat := ((18174751 : Rat) / 10000000)
def block226S2 : Rat := ((511587 : Rat) / 200000)
def block226S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block226S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block226V (y : ℝ) : ℝ :=
  ratPotential block226W1 block226W2 block226W3 block226W4 block226S1 block226S2 block226S3 block226S4 y

def block226LeftParamsCertificate : Bool :=
  allBoxesSameParams block226LeftBoxes block226W1 block226W2 block226W3 block226W4 block226S1 block226S2 block226S3 block226S4

theorem block226LeftParamsCertificate_eq_true :
    block226LeftParamsCertificate = true := by
  native_decide

theorem block226_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block226LeftL : ℝ) (block226LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block226S1 : ℝ))
    (hy2ne : y ≠ (block226S2 : ℝ))
    (hy3ne : y ≠ (block226S3 : ℝ))
    (hy4ne : y ≠ (block226S4 : ℝ)) :
    0 < block226V y := by
  have hcert := block226LeftCertificate_eq_true
  unfold block226LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block226LeftBoxes) (lo := block226LeftL) (hi := block226LeftR)
    (w1 := block226W1) (w2 := block226W2) (w3 := block226W3) (w4 := block226W4)
    (s1 := block226S1) (s2 := block226S2) (s3 := block226S3) (s4 := block226S4)
    hboxes hcover block226LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block226RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block226RightChunk000 block226W1 block226W2 block226W3 block226W4 block226S1 block226S2 block226S3 block226S4

theorem block226RightChunk000ParamsCertificate_eq_true :
    block226RightChunk000ParamsCertificate = true := by
  native_decide

theorem block226_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block226RightChunk000L : ℝ) (block226RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block226S1 : ℝ))
    (hy2ne : y ≠ (block226S2 : ℝ))
    (hy3ne : y ≠ (block226S3 : ℝ))
    (hy4ne : y ≠ (block226S4 : ℝ)) :
    0 < block226V y := by
  have hcert := block226RightChunk000Certificate_eq_true
  unfold block226RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block226RightChunk000) (lo := block226RightChunk000L) (hi := block226RightChunk000R)
    (w1 := block226W1) (w2 := block226W2) (w3 := block226W3) (w4 := block226W4)
    (s1 := block226S1) (s2 := block226S2) (s3 := block226S3) (s4 := block226S4)
    hboxes hcover block226RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block226RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block226RightChunk001 block226W1 block226W2 block226W3 block226W4 block226S1 block226S2 block226S3 block226S4

theorem block226RightChunk001ParamsCertificate_eq_true :
    block226RightChunk001ParamsCertificate = true := by
  native_decide

theorem block226_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block226RightChunk001L : ℝ) (block226RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block226S1 : ℝ))
    (hy2ne : y ≠ (block226S2 : ℝ))
    (hy3ne : y ≠ (block226S3 : ℝ))
    (hy4ne : y ≠ (block226S4 : ℝ)) :
    0 < block226V y := by
  have hcert := block226RightChunk001Certificate_eq_true
  unfold block226RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block226RightChunk001) (lo := block226RightChunk001L) (hi := block226RightChunk001R)
    (w1 := block226W1) (w2 := block226W2) (w3 := block226W3) (w4 := block226W4)
    (s1 := block226S1) (s2 := block226S2) (s3 := block226S3) (s4 := block226S4)
    hboxes hcover block226RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block226RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block226RightChunk002 block226W1 block226W2 block226W3 block226W4 block226S1 block226S2 block226S3 block226S4

theorem block226RightChunk002ParamsCertificate_eq_true :
    block226RightChunk002ParamsCertificate = true := by
  native_decide

theorem block226_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block226RightChunk002L : ℝ) (block226RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block226S1 : ℝ))
    (hy2ne : y ≠ (block226S2 : ℝ))
    (hy3ne : y ≠ (block226S3 : ℝ))
    (hy4ne : y ≠ (block226S4 : ℝ)) :
    0 < block226V y := by
  have hcert := block226RightChunk002Certificate_eq_true
  unfold block226RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block226RightChunk002) (lo := block226RightChunk002L) (hi := block226RightChunk002R)
    (w1 := block226W1) (w2 := block226W2) (w3 := block226W3) (w4 := block226W4)
    (s1 := block226S1) (s2 := block226S2) (s3 := block226S3) (s4 := block226S4)
    hboxes hcover block226RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block226_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block226RightL : ℝ) (block226RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block226S1 : ℝ))
    (hy2ne : y ≠ (block226S2 : ℝ))
    (hy3ne : y ≠ (block226S3 : ℝ))
    (hy4ne : y ≠ (block226S4 : ℝ)) :
    0 < block226V y := by
  by_cases h0 : y ≤ (block226RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block226RightChunk000L : ℝ) (block226RightChunk000R : ℝ) := by
      have hL : (block226RightChunk000L : ℝ) = (block226RightL : ℝ) := by
        norm_num [block226RightChunk000L, block226RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block226_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block226RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block226RightChunk001L : ℝ) (block226RightChunk001R : ℝ) := by
        have hprev : (block226RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block226RightChunk001L : ℝ) = (block226RightChunk000R : ℝ) := by
          norm_num [block226RightChunk001L, block226RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block226_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block226RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block226RightChunk002L : ℝ) = (block226RightChunk001R : ℝ) := by
        norm_num [block226RightChunk002L, block226RightChunk001R]
      have hR : (block226RightChunk002R : ℝ) = (block226RightR : ℝ) := by
        norm_num [block226RightChunk002R, block226RightR]
      have hyc : y ∈ Icc (block226RightChunk002L : ℝ) (block226RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block226_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block226_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block226LeftL : ℝ) (block226LeftR : ℝ) →
    y ≠ 0 → y ≠ (block226S1 : ℝ) → y ≠ (block226S2 : ℝ) →
    y ≠ (block226S3 : ℝ) → y ≠ (block226S4 : ℝ) → 0 < block226V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block226RightL : ℝ) (block226RightR : ℝ) →
    y ≠ 0 → y ≠ (block226S1 : ℝ) → y ≠ (block226S2 : ℝ) →
    y ≠ (block226S3 : ℝ) → y ≠ (block226S4 : ℝ) → 0 < block226V y)

theorem block226_reallog_certificate_proof :
    block226_reallog_certificate := by
  exact ⟨block226_left_V_pos, block226_right_V_pos⟩

end Block226
end M1817475
end Erdos1038Lean
