import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block203

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block203

open Set

def block203W1 : Rat := ((9708032183926577 : Rat) / 10000000000000000)
def block203W2 : Rat := ((103274929313389 : Rat) / 2000000000000000)
def block203W3 : Rat := ((17707510063751583 : Rat) / 100000000000000000)
def block203W4 : Rat := ((2411808650627401 : Rat) / 25000000000000000)
def block203S1 : Rat := ((18174751 : Rat) / 10000000)
def block203S2 : Rat := ((511587 : Rat) / 200000)
def block203S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block203S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block203V (y : ℝ) : ℝ :=
  ratPotential block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4 y

def block203LeftParamsCertificate : Bool :=
  allBoxesSameParams block203LeftBoxes block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4

theorem block203LeftParamsCertificate_eq_true :
    block203LeftParamsCertificate = true := by
  native_decide

theorem block203_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203LeftL : ℝ) (block203LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  have hcert := block203LeftCertificate_eq_true
  unfold block203LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block203LeftBoxes) (lo := block203LeftL) (hi := block203LeftR)
    (w1 := block203W1) (w2 := block203W2) (w3 := block203W3) (w4 := block203W4)
    (s1 := block203S1) (s2 := block203S2) (s3 := block203S3) (s4 := block203S4)
    hboxes hcover block203LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block203RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block203RightChunk000 block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4

theorem block203RightChunk000ParamsCertificate_eq_true :
    block203RightChunk000ParamsCertificate = true := by
  native_decide

theorem block203_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203RightChunk000L : ℝ) (block203RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  have hcert := block203RightChunk000Certificate_eq_true
  unfold block203RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block203RightChunk000) (lo := block203RightChunk000L) (hi := block203RightChunk000R)
    (w1 := block203W1) (w2 := block203W2) (w3 := block203W3) (w4 := block203W4)
    (s1 := block203S1) (s2 := block203S2) (s3 := block203S3) (s4 := block203S4)
    hboxes hcover block203RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block203RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block203RightChunk001 block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4

theorem block203RightChunk001ParamsCertificate_eq_true :
    block203RightChunk001ParamsCertificate = true := by
  native_decide

theorem block203_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203RightChunk001L : ℝ) (block203RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  have hcert := block203RightChunk001Certificate_eq_true
  unfold block203RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block203RightChunk001) (lo := block203RightChunk001L) (hi := block203RightChunk001R)
    (w1 := block203W1) (w2 := block203W2) (w3 := block203W3) (w4 := block203W4)
    (s1 := block203S1) (s2 := block203S2) (s3 := block203S3) (s4 := block203S4)
    hboxes hcover block203RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block203RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block203RightChunk002 block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4

theorem block203RightChunk002ParamsCertificate_eq_true :
    block203RightChunk002ParamsCertificate = true := by
  native_decide

theorem block203_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203RightChunk002L : ℝ) (block203RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  have hcert := block203RightChunk002Certificate_eq_true
  unfold block203RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block203RightChunk002) (lo := block203RightChunk002L) (hi := block203RightChunk002R)
    (w1 := block203W1) (w2 := block203W2) (w3 := block203W3) (w4 := block203W4)
    (s1 := block203S1) (s2 := block203S2) (s3 := block203S3) (s4 := block203S4)
    hboxes hcover block203RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block203RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block203RightChunk003 block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4

theorem block203RightChunk003ParamsCertificate_eq_true :
    block203RightChunk003ParamsCertificate = true := by
  native_decide

theorem block203_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203RightChunk003L : ℝ) (block203RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  have hcert := block203RightChunk003Certificate_eq_true
  unfold block203RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block203RightChunk003) (lo := block203RightChunk003L) (hi := block203RightChunk003R)
    (w1 := block203W1) (w2 := block203W2) (w3 := block203W3) (w4 := block203W4)
    (s1 := block203S1) (s2 := block203S2) (s3 := block203S3) (s4 := block203S4)
    hboxes hcover block203RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block203RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block203RightChunk004 block203W1 block203W2 block203W3 block203W4 block203S1 block203S2 block203S3 block203S4

theorem block203RightChunk004ParamsCertificate_eq_true :
    block203RightChunk004ParamsCertificate = true := by
  native_decide

theorem block203_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203RightChunk004L : ℝ) (block203RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  have hcert := block203RightChunk004Certificate_eq_true
  unfold block203RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block203RightChunk004) (lo := block203RightChunk004L) (hi := block203RightChunk004R)
    (w1 := block203W1) (w2 := block203W2) (w3 := block203W3) (w4 := block203W4)
    (s1 := block203S1) (s2 := block203S2) (s3 := block203S3) (s4 := block203S4)
    hboxes hcover block203RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block203_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block203RightL : ℝ) (block203RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block203S1 : ℝ))
    (hy2ne : y ≠ (block203S2 : ℝ))
    (hy3ne : y ≠ (block203S3 : ℝ))
    (hy4ne : y ≠ (block203S4 : ℝ)) :
    0 < block203V y := by
  by_cases h0 : y ≤ (block203RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block203RightChunk000L : ℝ) (block203RightChunk000R : ℝ) := by
      have hL : (block203RightChunk000L : ℝ) = (block203RightL : ℝ) := by
        norm_num [block203RightChunk000L, block203RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block203_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block203RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block203RightChunk001L : ℝ) (block203RightChunk001R : ℝ) := by
        have hprev : (block203RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block203RightChunk001L : ℝ) = (block203RightChunk000R : ℝ) := by
          norm_num [block203RightChunk001L, block203RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block203_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block203RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block203RightChunk002L : ℝ) (block203RightChunk002R : ℝ) := by
          have hprev : (block203RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block203RightChunk002L : ℝ) = (block203RightChunk001R : ℝ) := by
            norm_num [block203RightChunk002L, block203RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block203_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block203RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block203RightChunk003L : ℝ) (block203RightChunk003R : ℝ) := by
            have hprev : (block203RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block203RightChunk003L : ℝ) = (block203RightChunk002R : ℝ) := by
              norm_num [block203RightChunk003L, block203RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block203_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          have hprev : (block203RightChunk003R : ℝ) < y := lt_of_not_ge h3
          have hL : (block203RightChunk004L : ℝ) = (block203RightChunk003R : ℝ) := by
            norm_num [block203RightChunk004L, block203RightChunk003R]
          have hR : (block203RightChunk004R : ℝ) = (block203RightR : ℝ) := by
            norm_num [block203RightChunk004R, block203RightR]
          have hyc : y ∈ Icc (block203RightChunk004L : ℝ) (block203RightChunk004R : ℝ) := by
            constructor
            · linarith [hprev, hL]
            · linarith [hy.2, hR]
          exact block203_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block203_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block203LeftL : ℝ) (block203LeftR : ℝ) →
    y ≠ 0 → y ≠ (block203S1 : ℝ) → y ≠ (block203S2 : ℝ) →
    y ≠ (block203S3 : ℝ) → y ≠ (block203S4 : ℝ) → 0 < block203V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block203RightL : ℝ) (block203RightR : ℝ) →
    y ≠ 0 → y ≠ (block203S1 : ℝ) → y ≠ (block203S2 : ℝ) →
    y ≠ (block203S3 : ℝ) → y ≠ (block203S4 : ℝ) → 0 < block203V y)

theorem block203_reallog_certificate_proof :
    block203_reallog_certificate := by
  exact ⟨block203_left_V_pos, block203_right_V_pos⟩

end Block203
end M1817475
end Erdos1038Lean
