import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block193

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block193

open Set

def block193W1 : Rat := ((17415453303190247 : Rat) / 10000000000000000)
def block193W2 : Rat := (0 : Rat)
def block193W3 : Rat := ((18126145154781803 : Rat) / 100000000000000000)
def block193W4 : Rat := ((1832846315306479 : Rat) / 20000000000000000)
def block193S1 : Rat := ((18174751 : Rat) / 10000000)
def block193S2 : Rat := ((511587 : Rat) / 200000)
def block193S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block193S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block193V (y : ℝ) : ℝ :=
  ratPotential block193W1 block193W2 block193W3 block193W4 block193S1 block193S2 block193S3 block193S4 y

def block193LeftParamsCertificate : Bool :=
  allBoxesSameParams block193LeftBoxes block193W1 block193W2 block193W3 block193W4 block193S1 block193S2 block193S3 block193S4

theorem block193LeftParamsCertificate_eq_true :
    block193LeftParamsCertificate = true := by
  native_decide

theorem block193_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block193LeftL : ℝ) (block193LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block193S1 : ℝ))
    (hy2ne : y ≠ (block193S2 : ℝ))
    (hy3ne : y ≠ (block193S3 : ℝ))
    (hy4ne : y ≠ (block193S4 : ℝ)) :
    0 < block193V y := by
  have hcert := block193LeftCertificate_eq_true
  unfold block193LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block193LeftBoxes) (lo := block193LeftL) (hi := block193LeftR)
    (w1 := block193W1) (w2 := block193W2) (w3 := block193W3) (w4 := block193W4)
    (s1 := block193S1) (s2 := block193S2) (s3 := block193S3) (s4 := block193S4)
    hboxes hcover block193LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block193RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block193RightChunk000 block193W1 block193W2 block193W3 block193W4 block193S1 block193S2 block193S3 block193S4

theorem block193RightChunk000ParamsCertificate_eq_true :
    block193RightChunk000ParamsCertificate = true := by
  native_decide

theorem block193_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block193RightChunk000L : ℝ) (block193RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block193S1 : ℝ))
    (hy2ne : y ≠ (block193S2 : ℝ))
    (hy3ne : y ≠ (block193S3 : ℝ))
    (hy4ne : y ≠ (block193S4 : ℝ)) :
    0 < block193V y := by
  have hcert := block193RightChunk000Certificate_eq_true
  unfold block193RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block193RightChunk000) (lo := block193RightChunk000L) (hi := block193RightChunk000R)
    (w1 := block193W1) (w2 := block193W2) (w3 := block193W3) (w4 := block193W4)
    (s1 := block193S1) (s2 := block193S2) (s3 := block193S3) (s4 := block193S4)
    hboxes hcover block193RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block193RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block193RightChunk001 block193W1 block193W2 block193W3 block193W4 block193S1 block193S2 block193S3 block193S4

theorem block193RightChunk001ParamsCertificate_eq_true :
    block193RightChunk001ParamsCertificate = true := by
  native_decide

theorem block193_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block193RightChunk001L : ℝ) (block193RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block193S1 : ℝ))
    (hy2ne : y ≠ (block193S2 : ℝ))
    (hy3ne : y ≠ (block193S3 : ℝ))
    (hy4ne : y ≠ (block193S4 : ℝ)) :
    0 < block193V y := by
  have hcert := block193RightChunk001Certificate_eq_true
  unfold block193RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block193RightChunk001) (lo := block193RightChunk001L) (hi := block193RightChunk001R)
    (w1 := block193W1) (w2 := block193W2) (w3 := block193W3) (w4 := block193W4)
    (s1 := block193S1) (s2 := block193S2) (s3 := block193S3) (s4 := block193S4)
    hboxes hcover block193RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block193RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block193RightChunk002 block193W1 block193W2 block193W3 block193W4 block193S1 block193S2 block193S3 block193S4

theorem block193RightChunk002ParamsCertificate_eq_true :
    block193RightChunk002ParamsCertificate = true := by
  native_decide

theorem block193_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block193RightChunk002L : ℝ) (block193RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block193S1 : ℝ))
    (hy2ne : y ≠ (block193S2 : ℝ))
    (hy3ne : y ≠ (block193S3 : ℝ))
    (hy4ne : y ≠ (block193S4 : ℝ)) :
    0 < block193V y := by
  have hcert := block193RightChunk002Certificate_eq_true
  unfold block193RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block193RightChunk002) (lo := block193RightChunk002L) (hi := block193RightChunk002R)
    (w1 := block193W1) (w2 := block193W2) (w3 := block193W3) (w4 := block193W4)
    (s1 := block193S1) (s2 := block193S2) (s3 := block193S3) (s4 := block193S4)
    hboxes hcover block193RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block193RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block193RightChunk003 block193W1 block193W2 block193W3 block193W4 block193S1 block193S2 block193S3 block193S4

theorem block193RightChunk003ParamsCertificate_eq_true :
    block193RightChunk003ParamsCertificate = true := by
  native_decide

theorem block193_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block193RightChunk003L : ℝ) (block193RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block193S1 : ℝ))
    (hy2ne : y ≠ (block193S2 : ℝ))
    (hy3ne : y ≠ (block193S3 : ℝ))
    (hy4ne : y ≠ (block193S4 : ℝ)) :
    0 < block193V y := by
  have hcert := block193RightChunk003Certificate_eq_true
  unfold block193RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block193RightChunk003) (lo := block193RightChunk003L) (hi := block193RightChunk003R)
    (w1 := block193W1) (w2 := block193W2) (w3 := block193W3) (w4 := block193W4)
    (s1 := block193S1) (s2 := block193S2) (s3 := block193S3) (s4 := block193S4)
    hboxes hcover block193RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block193_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block193RightL : ℝ) (block193RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block193S1 : ℝ))
    (hy2ne : y ≠ (block193S2 : ℝ))
    (hy3ne : y ≠ (block193S3 : ℝ))
    (hy4ne : y ≠ (block193S4 : ℝ)) :
    0 < block193V y := by
  by_cases h0 : y ≤ (block193RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block193RightChunk000L : ℝ) (block193RightChunk000R : ℝ) := by
      have hL : (block193RightChunk000L : ℝ) = (block193RightL : ℝ) := by
        norm_num [block193RightChunk000L, block193RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block193_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block193RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block193RightChunk001L : ℝ) (block193RightChunk001R : ℝ) := by
        have hprev : (block193RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block193RightChunk001L : ℝ) = (block193RightChunk000R : ℝ) := by
          norm_num [block193RightChunk001L, block193RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block193_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block193RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block193RightChunk002L : ℝ) (block193RightChunk002R : ℝ) := by
          have hprev : (block193RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block193RightChunk002L : ℝ) = (block193RightChunk001R : ℝ) := by
            norm_num [block193RightChunk002L, block193RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block193_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block193RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block193RightChunk003L : ℝ) = (block193RightChunk002R : ℝ) := by
          norm_num [block193RightChunk003L, block193RightChunk002R]
        have hR : (block193RightChunk003R : ℝ) = (block193RightR : ℝ) := by
          norm_num [block193RightChunk003R, block193RightR]
        have hyc : y ∈ Icc (block193RightChunk003L : ℝ) (block193RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block193_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block193_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block193LeftL : ℝ) (block193LeftR : ℝ) →
    y ≠ 0 → y ≠ (block193S1 : ℝ) → y ≠ (block193S2 : ℝ) →
    y ≠ (block193S3 : ℝ) → y ≠ (block193S4 : ℝ) → 0 < block193V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block193RightL : ℝ) (block193RightR : ℝ) →
    y ≠ 0 → y ≠ (block193S1 : ℝ) → y ≠ (block193S2 : ℝ) →
    y ≠ (block193S3 : ℝ) → y ≠ (block193S4 : ℝ) → 0 < block193V y)

theorem block193_reallog_certificate_proof :
    block193_reallog_certificate := by
  exact ⟨block193_left_V_pos, block193_right_V_pos⟩

end Block193
end M1817475
end Erdos1038Lean
