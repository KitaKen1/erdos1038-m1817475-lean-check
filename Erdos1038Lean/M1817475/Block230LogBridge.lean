import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block230

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block230

open Set

def block230W1 : Rat := ((8660279197092767 : Rat) / 10000000000000000)
def block230W2 : Rat := ((8312536673520603 : Rat) / 100000000000000000)
def block230W3 : Rat := ((1827536918841983 : Rat) / 10000000000000000)
def block230W4 : Rat := ((7034954657988879 : Rat) / 100000000000000000)
def block230S1 : Rat := ((18174751 : Rat) / 10000000)
def block230S2 : Rat := ((511587 : Rat) / 200000)
def block230S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block230S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block230V (y : ℝ) : ℝ :=
  ratPotential block230W1 block230W2 block230W3 block230W4 block230S1 block230S2 block230S3 block230S4 y

def block230LeftParamsCertificate : Bool :=
  allBoxesSameParams block230LeftBoxes block230W1 block230W2 block230W3 block230W4 block230S1 block230S2 block230S3 block230S4

theorem block230LeftParamsCertificate_eq_true :
    block230LeftParamsCertificate = true := by
  native_decide

theorem block230_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block230LeftL : ℝ) (block230LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block230S1 : ℝ))
    (hy2ne : y ≠ (block230S2 : ℝ))
    (hy3ne : y ≠ (block230S3 : ℝ))
    (hy4ne : y ≠ (block230S4 : ℝ)) :
    0 < block230V y := by
  have hcert := block230LeftCertificate_eq_true
  unfold block230LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block230LeftBoxes) (lo := block230LeftL) (hi := block230LeftR)
    (w1 := block230W1) (w2 := block230W2) (w3 := block230W3) (w4 := block230W4)
    (s1 := block230S1) (s2 := block230S2) (s3 := block230S3) (s4 := block230S4)
    hboxes hcover block230LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block230RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block230RightChunk000 block230W1 block230W2 block230W3 block230W4 block230S1 block230S2 block230S3 block230S4

theorem block230RightChunk000ParamsCertificate_eq_true :
    block230RightChunk000ParamsCertificate = true := by
  native_decide

theorem block230_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block230RightChunk000L : ℝ) (block230RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block230S1 : ℝ))
    (hy2ne : y ≠ (block230S2 : ℝ))
    (hy3ne : y ≠ (block230S3 : ℝ))
    (hy4ne : y ≠ (block230S4 : ℝ)) :
    0 < block230V y := by
  have hcert := block230RightChunk000Certificate_eq_true
  unfold block230RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block230RightChunk000) (lo := block230RightChunk000L) (hi := block230RightChunk000R)
    (w1 := block230W1) (w2 := block230W2) (w3 := block230W3) (w4 := block230W4)
    (s1 := block230S1) (s2 := block230S2) (s3 := block230S3) (s4 := block230S4)
    hboxes hcover block230RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block230RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block230RightChunk001 block230W1 block230W2 block230W3 block230W4 block230S1 block230S2 block230S3 block230S4

theorem block230RightChunk001ParamsCertificate_eq_true :
    block230RightChunk001ParamsCertificate = true := by
  native_decide

theorem block230_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block230RightChunk001L : ℝ) (block230RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block230S1 : ℝ))
    (hy2ne : y ≠ (block230S2 : ℝ))
    (hy3ne : y ≠ (block230S3 : ℝ))
    (hy4ne : y ≠ (block230S4 : ℝ)) :
    0 < block230V y := by
  have hcert := block230RightChunk001Certificate_eq_true
  unfold block230RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block230RightChunk001) (lo := block230RightChunk001L) (hi := block230RightChunk001R)
    (w1 := block230W1) (w2 := block230W2) (w3 := block230W3) (w4 := block230W4)
    (s1 := block230S1) (s2 := block230S2) (s3 := block230S3) (s4 := block230S4)
    hboxes hcover block230RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block230RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block230RightChunk002 block230W1 block230W2 block230W3 block230W4 block230S1 block230S2 block230S3 block230S4

theorem block230RightChunk002ParamsCertificate_eq_true :
    block230RightChunk002ParamsCertificate = true := by
  native_decide

theorem block230_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block230RightChunk002L : ℝ) (block230RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block230S1 : ℝ))
    (hy2ne : y ≠ (block230S2 : ℝ))
    (hy3ne : y ≠ (block230S3 : ℝ))
    (hy4ne : y ≠ (block230S4 : ℝ)) :
    0 < block230V y := by
  have hcert := block230RightChunk002Certificate_eq_true
  unfold block230RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block230RightChunk002) (lo := block230RightChunk002L) (hi := block230RightChunk002R)
    (w1 := block230W1) (w2 := block230W2) (w3 := block230W3) (w4 := block230W4)
    (s1 := block230S1) (s2 := block230S2) (s3 := block230S3) (s4 := block230S4)
    hboxes hcover block230RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block230_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block230RightL : ℝ) (block230RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block230S1 : ℝ))
    (hy2ne : y ≠ (block230S2 : ℝ))
    (hy3ne : y ≠ (block230S3 : ℝ))
    (hy4ne : y ≠ (block230S4 : ℝ)) :
    0 < block230V y := by
  by_cases h0 : y ≤ (block230RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block230RightChunk000L : ℝ) (block230RightChunk000R : ℝ) := by
      have hL : (block230RightChunk000L : ℝ) = (block230RightL : ℝ) := by
        norm_num [block230RightChunk000L, block230RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block230_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block230RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block230RightChunk001L : ℝ) (block230RightChunk001R : ℝ) := by
        have hprev : (block230RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block230RightChunk001L : ℝ) = (block230RightChunk000R : ℝ) := by
          norm_num [block230RightChunk001L, block230RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block230_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block230RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block230RightChunk002L : ℝ) = (block230RightChunk001R : ℝ) := by
        norm_num [block230RightChunk002L, block230RightChunk001R]
      have hR : (block230RightChunk002R : ℝ) = (block230RightR : ℝ) := by
        norm_num [block230RightChunk002R, block230RightR]
      have hyc : y ∈ Icc (block230RightChunk002L : ℝ) (block230RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block230_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block230_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block230LeftL : ℝ) (block230LeftR : ℝ) →
    y ≠ 0 → y ≠ (block230S1 : ℝ) → y ≠ (block230S2 : ℝ) →
    y ≠ (block230S3 : ℝ) → y ≠ (block230S4 : ℝ) → 0 < block230V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block230RightL : ℝ) (block230RightR : ℝ) →
    y ≠ 0 → y ≠ (block230S1 : ℝ) → y ≠ (block230S2 : ℝ) →
    y ≠ (block230S3 : ℝ) → y ≠ (block230S4 : ℝ) → 0 < block230V y)

theorem block230_reallog_certificate_proof :
    block230_reallog_certificate := by
  exact ⟨block230_left_V_pos, block230_right_V_pos⟩

end Block230
end M1817475
end Erdos1038Lean
