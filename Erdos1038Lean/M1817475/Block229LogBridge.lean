import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block229

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block229

open Set

def block229W1 : Rat := ((17339703133447 : Rat) / 20000000000000)
def block229W2 : Rat := ((8276441981619417 : Rat) / 100000000000000000)
def block229W3 : Rat := ((9159448480100023 : Rat) / 50000000000000000)
def block229W4 : Rat := ((3507830362241259 : Rat) / 50000000000000000)
def block229S1 : Rat := ((18174751 : Rat) / 10000000)
def block229S2 : Rat := ((511587 : Rat) / 200000)
def block229S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block229S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block229V (y : ℝ) : ℝ :=
  ratPotential block229W1 block229W2 block229W3 block229W4 block229S1 block229S2 block229S3 block229S4 y

def block229LeftParamsCertificate : Bool :=
  allBoxesSameParams block229LeftBoxes block229W1 block229W2 block229W3 block229W4 block229S1 block229S2 block229S3 block229S4

theorem block229LeftParamsCertificate_eq_true :
    block229LeftParamsCertificate = true := by
  native_decide

theorem block229_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block229LeftL : ℝ) (block229LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block229S1 : ℝ))
    (hy2ne : y ≠ (block229S2 : ℝ))
    (hy3ne : y ≠ (block229S3 : ℝ))
    (hy4ne : y ≠ (block229S4 : ℝ)) :
    0 < block229V y := by
  have hcert := block229LeftCertificate_eq_true
  unfold block229LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block229LeftBoxes) (lo := block229LeftL) (hi := block229LeftR)
    (w1 := block229W1) (w2 := block229W2) (w3 := block229W3) (w4 := block229W4)
    (s1 := block229S1) (s2 := block229S2) (s3 := block229S3) (s4 := block229S4)
    hboxes hcover block229LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block229RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block229RightChunk000 block229W1 block229W2 block229W3 block229W4 block229S1 block229S2 block229S3 block229S4

theorem block229RightChunk000ParamsCertificate_eq_true :
    block229RightChunk000ParamsCertificate = true := by
  native_decide

theorem block229_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block229RightChunk000L : ℝ) (block229RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block229S1 : ℝ))
    (hy2ne : y ≠ (block229S2 : ℝ))
    (hy3ne : y ≠ (block229S3 : ℝ))
    (hy4ne : y ≠ (block229S4 : ℝ)) :
    0 < block229V y := by
  have hcert := block229RightChunk000Certificate_eq_true
  unfold block229RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block229RightChunk000) (lo := block229RightChunk000L) (hi := block229RightChunk000R)
    (w1 := block229W1) (w2 := block229W2) (w3 := block229W3) (w4 := block229W4)
    (s1 := block229S1) (s2 := block229S2) (s3 := block229S3) (s4 := block229S4)
    hboxes hcover block229RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block229RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block229RightChunk001 block229W1 block229W2 block229W3 block229W4 block229S1 block229S2 block229S3 block229S4

theorem block229RightChunk001ParamsCertificate_eq_true :
    block229RightChunk001ParamsCertificate = true := by
  native_decide

theorem block229_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block229RightChunk001L : ℝ) (block229RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block229S1 : ℝ))
    (hy2ne : y ≠ (block229S2 : ℝ))
    (hy3ne : y ≠ (block229S3 : ℝ))
    (hy4ne : y ≠ (block229S4 : ℝ)) :
    0 < block229V y := by
  have hcert := block229RightChunk001Certificate_eq_true
  unfold block229RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block229RightChunk001) (lo := block229RightChunk001L) (hi := block229RightChunk001R)
    (w1 := block229W1) (w2 := block229W2) (w3 := block229W3) (w4 := block229W4)
    (s1 := block229S1) (s2 := block229S2) (s3 := block229S3) (s4 := block229S4)
    hboxes hcover block229RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block229RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block229RightChunk002 block229W1 block229W2 block229W3 block229W4 block229S1 block229S2 block229S3 block229S4

theorem block229RightChunk002ParamsCertificate_eq_true :
    block229RightChunk002ParamsCertificate = true := by
  native_decide

theorem block229_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block229RightChunk002L : ℝ) (block229RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block229S1 : ℝ))
    (hy2ne : y ≠ (block229S2 : ℝ))
    (hy3ne : y ≠ (block229S3 : ℝ))
    (hy4ne : y ≠ (block229S4 : ℝ)) :
    0 < block229V y := by
  have hcert := block229RightChunk002Certificate_eq_true
  unfold block229RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block229RightChunk002) (lo := block229RightChunk002L) (hi := block229RightChunk002R)
    (w1 := block229W1) (w2 := block229W2) (w3 := block229W3) (w4 := block229W4)
    (s1 := block229S1) (s2 := block229S2) (s3 := block229S3) (s4 := block229S4)
    hboxes hcover block229RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block229_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block229RightL : ℝ) (block229RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block229S1 : ℝ))
    (hy2ne : y ≠ (block229S2 : ℝ))
    (hy3ne : y ≠ (block229S3 : ℝ))
    (hy4ne : y ≠ (block229S4 : ℝ)) :
    0 < block229V y := by
  by_cases h0 : y ≤ (block229RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block229RightChunk000L : ℝ) (block229RightChunk000R : ℝ) := by
      have hL : (block229RightChunk000L : ℝ) = (block229RightL : ℝ) := by
        norm_num [block229RightChunk000L, block229RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block229_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block229RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block229RightChunk001L : ℝ) (block229RightChunk001R : ℝ) := by
        have hprev : (block229RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block229RightChunk001L : ℝ) = (block229RightChunk000R : ℝ) := by
          norm_num [block229RightChunk001L, block229RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block229_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block229RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block229RightChunk002L : ℝ) = (block229RightChunk001R : ℝ) := by
        norm_num [block229RightChunk002L, block229RightChunk001R]
      have hR : (block229RightChunk002R : ℝ) = (block229RightR : ℝ) := by
        norm_num [block229RightChunk002R, block229RightR]
      have hyc : y ∈ Icc (block229RightChunk002L : ℝ) (block229RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block229_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block229_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block229LeftL : ℝ) (block229LeftR : ℝ) →
    y ≠ 0 → y ≠ (block229S1 : ℝ) → y ≠ (block229S2 : ℝ) →
    y ≠ (block229S3 : ℝ) → y ≠ (block229S4 : ℝ) → 0 < block229V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block229RightL : ℝ) (block229RightR : ℝ) →
    y ≠ 0 → y ≠ (block229S1 : ℝ) → y ≠ (block229S2 : ℝ) →
    y ≠ (block229S3 : ℝ) → y ≠ (block229S4 : ℝ) → 0 < block229V y)

theorem block229_reallog_certificate_proof :
    block229_reallog_certificate := by
  exact ⟨block229_left_V_pos, block229_right_V_pos⟩

end Block229
end M1817475
end Erdos1038Lean
