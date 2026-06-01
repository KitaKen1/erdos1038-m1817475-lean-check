import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block192

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block192

open Set

def block192W1 : Rat := ((17450666056058701 : Rat) / 10000000000000000)
def block192W2 : Rat := (0 : Rat)
def block192W3 : Rat := ((722644722741417 : Rat) / 4000000000000000)
def block192W4 : Rat := ((4602855035002809 : Rat) / 50000000000000000)
def block192S1 : Rat := ((18174751 : Rat) / 10000000)
def block192S2 : Rat := ((511587 : Rat) / 200000)
def block192S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block192S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block192V (y : ℝ) : ℝ :=
  ratPotential block192W1 block192W2 block192W3 block192W4 block192S1 block192S2 block192S3 block192S4 y

def block192LeftParamsCertificate : Bool :=
  allBoxesSameParams block192LeftBoxes block192W1 block192W2 block192W3 block192W4 block192S1 block192S2 block192S3 block192S4

theorem block192LeftParamsCertificate_eq_true :
    block192LeftParamsCertificate = true := by
  native_decide

theorem block192_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block192LeftL : ℝ) (block192LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block192S1 : ℝ))
    (hy2ne : y ≠ (block192S2 : ℝ))
    (hy3ne : y ≠ (block192S3 : ℝ))
    (hy4ne : y ≠ (block192S4 : ℝ)) :
    0 < block192V y := by
  have hcert := block192LeftCertificate_eq_true
  unfold block192LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block192LeftBoxes) (lo := block192LeftL) (hi := block192LeftR)
    (w1 := block192W1) (w2 := block192W2) (w3 := block192W3) (w4 := block192W4)
    (s1 := block192S1) (s2 := block192S2) (s3 := block192S3) (s4 := block192S4)
    hboxes hcover block192LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block192RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block192RightChunk000 block192W1 block192W2 block192W3 block192W4 block192S1 block192S2 block192S3 block192S4

theorem block192RightChunk000ParamsCertificate_eq_true :
    block192RightChunk000ParamsCertificate = true := by
  native_decide

theorem block192_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block192RightChunk000L : ℝ) (block192RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block192S1 : ℝ))
    (hy2ne : y ≠ (block192S2 : ℝ))
    (hy3ne : y ≠ (block192S3 : ℝ))
    (hy4ne : y ≠ (block192S4 : ℝ)) :
    0 < block192V y := by
  have hcert := block192RightChunk000Certificate_eq_true
  unfold block192RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block192RightChunk000) (lo := block192RightChunk000L) (hi := block192RightChunk000R)
    (w1 := block192W1) (w2 := block192W2) (w3 := block192W3) (w4 := block192W4)
    (s1 := block192S1) (s2 := block192S2) (s3 := block192S3) (s4 := block192S4)
    hboxes hcover block192RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block192RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block192RightChunk001 block192W1 block192W2 block192W3 block192W4 block192S1 block192S2 block192S3 block192S4

theorem block192RightChunk001ParamsCertificate_eq_true :
    block192RightChunk001ParamsCertificate = true := by
  native_decide

theorem block192_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block192RightChunk001L : ℝ) (block192RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block192S1 : ℝ))
    (hy2ne : y ≠ (block192S2 : ℝ))
    (hy3ne : y ≠ (block192S3 : ℝ))
    (hy4ne : y ≠ (block192S4 : ℝ)) :
    0 < block192V y := by
  have hcert := block192RightChunk001Certificate_eq_true
  unfold block192RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block192RightChunk001) (lo := block192RightChunk001L) (hi := block192RightChunk001R)
    (w1 := block192W1) (w2 := block192W2) (w3 := block192W3) (w4 := block192W4)
    (s1 := block192S1) (s2 := block192S2) (s3 := block192S3) (s4 := block192S4)
    hboxes hcover block192RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block192RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block192RightChunk002 block192W1 block192W2 block192W3 block192W4 block192S1 block192S2 block192S3 block192S4

theorem block192RightChunk002ParamsCertificate_eq_true :
    block192RightChunk002ParamsCertificate = true := by
  native_decide

theorem block192_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block192RightChunk002L : ℝ) (block192RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block192S1 : ℝ))
    (hy2ne : y ≠ (block192S2 : ℝ))
    (hy3ne : y ≠ (block192S3 : ℝ))
    (hy4ne : y ≠ (block192S4 : ℝ)) :
    0 < block192V y := by
  have hcert := block192RightChunk002Certificate_eq_true
  unfold block192RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block192RightChunk002) (lo := block192RightChunk002L) (hi := block192RightChunk002R)
    (w1 := block192W1) (w2 := block192W2) (w3 := block192W3) (w4 := block192W4)
    (s1 := block192S1) (s2 := block192S2) (s3 := block192S3) (s4 := block192S4)
    hboxes hcover block192RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block192_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block192RightL : ℝ) (block192RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block192S1 : ℝ))
    (hy2ne : y ≠ (block192S2 : ℝ))
    (hy3ne : y ≠ (block192S3 : ℝ))
    (hy4ne : y ≠ (block192S4 : ℝ)) :
    0 < block192V y := by
  by_cases h0 : y ≤ (block192RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block192RightChunk000L : ℝ) (block192RightChunk000R : ℝ) := by
      have hL : (block192RightChunk000L : ℝ) = (block192RightL : ℝ) := by
        norm_num [block192RightChunk000L, block192RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block192_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block192RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block192RightChunk001L : ℝ) (block192RightChunk001R : ℝ) := by
        have hprev : (block192RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block192RightChunk001L : ℝ) = (block192RightChunk000R : ℝ) := by
          norm_num [block192RightChunk001L, block192RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block192_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block192RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block192RightChunk002L : ℝ) = (block192RightChunk001R : ℝ) := by
        norm_num [block192RightChunk002L, block192RightChunk001R]
      have hR : (block192RightChunk002R : ℝ) = (block192RightR : ℝ) := by
        norm_num [block192RightChunk002R, block192RightR]
      have hyc : y ∈ Icc (block192RightChunk002L : ℝ) (block192RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block192_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block192_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block192LeftL : ℝ) (block192LeftR : ℝ) →
    y ≠ 0 → y ≠ (block192S1 : ℝ) → y ≠ (block192S2 : ℝ) →
    y ≠ (block192S3 : ℝ) → y ≠ (block192S4 : ℝ) → 0 < block192V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block192RightL : ℝ) (block192RightR : ℝ) →
    y ≠ 0 → y ≠ (block192S1 : ℝ) → y ≠ (block192S2 : ℝ) →
    y ≠ (block192S3 : ℝ) → y ≠ (block192S4 : ℝ) → 0 < block192V y)

theorem block192_reallog_certificate_proof :
    block192_reallog_certificate := by
  exact ⟨block192_left_V_pos, block192_right_V_pos⟩

end Block192
end M1817475
end Erdos1038Lean
