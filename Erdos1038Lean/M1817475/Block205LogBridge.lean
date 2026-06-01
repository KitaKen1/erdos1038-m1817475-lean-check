import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block205

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block205

open Set

def block205W1 : Rat := ((2424164552774051 : Rat) / 2500000000000000)
def block205W2 : Rat := ((25996842476334707 : Rat) / 500000000000000000)
def block205W3 : Rat := ((4415307095067611 : Rat) / 25000000000000000)
def block205W4 : Rat := ((9669886614160797 : Rat) / 100000000000000000)
def block205S1 : Rat := ((18174751 : Rat) / 10000000)
def block205S2 : Rat := ((511587 : Rat) / 200000)
def block205S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block205S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block205V (y : ℝ) : ℝ :=
  ratPotential block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4 y

def block205LeftParamsCertificate : Bool :=
  allBoxesSameParams block205LeftBoxes block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4

theorem block205LeftParamsCertificate_eq_true :
    block205LeftParamsCertificate = true := by
  native_decide

theorem block205_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205LeftL : ℝ) (block205LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  have hcert := block205LeftCertificate_eq_true
  unfold block205LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block205LeftBoxes) (lo := block205LeftL) (hi := block205LeftR)
    (w1 := block205W1) (w2 := block205W2) (w3 := block205W3) (w4 := block205W4)
    (s1 := block205S1) (s2 := block205S2) (s3 := block205S3) (s4 := block205S4)
    hboxes hcover block205LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block205RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block205RightChunk000 block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4

theorem block205RightChunk000ParamsCertificate_eq_true :
    block205RightChunk000ParamsCertificate = true := by
  native_decide

theorem block205_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205RightChunk000L : ℝ) (block205RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  have hcert := block205RightChunk000Certificate_eq_true
  unfold block205RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block205RightChunk000) (lo := block205RightChunk000L) (hi := block205RightChunk000R)
    (w1 := block205W1) (w2 := block205W2) (w3 := block205W3) (w4 := block205W4)
    (s1 := block205S1) (s2 := block205S2) (s3 := block205S3) (s4 := block205S4)
    hboxes hcover block205RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block205RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block205RightChunk001 block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4

theorem block205RightChunk001ParamsCertificate_eq_true :
    block205RightChunk001ParamsCertificate = true := by
  native_decide

theorem block205_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205RightChunk001L : ℝ) (block205RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  have hcert := block205RightChunk001Certificate_eq_true
  unfold block205RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block205RightChunk001) (lo := block205RightChunk001L) (hi := block205RightChunk001R)
    (w1 := block205W1) (w2 := block205W2) (w3 := block205W3) (w4 := block205W4)
    (s1 := block205S1) (s2 := block205S2) (s3 := block205S3) (s4 := block205S4)
    hboxes hcover block205RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block205RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block205RightChunk002 block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4

theorem block205RightChunk002ParamsCertificate_eq_true :
    block205RightChunk002ParamsCertificate = true := by
  native_decide

theorem block205_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205RightChunk002L : ℝ) (block205RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  have hcert := block205RightChunk002Certificate_eq_true
  unfold block205RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block205RightChunk002) (lo := block205RightChunk002L) (hi := block205RightChunk002R)
    (w1 := block205W1) (w2 := block205W2) (w3 := block205W3) (w4 := block205W4)
    (s1 := block205S1) (s2 := block205S2) (s3 := block205S3) (s4 := block205S4)
    hboxes hcover block205RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block205RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block205RightChunk003 block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4

theorem block205RightChunk003ParamsCertificate_eq_true :
    block205RightChunk003ParamsCertificate = true := by
  native_decide

theorem block205_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205RightChunk003L : ℝ) (block205RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  have hcert := block205RightChunk003Certificate_eq_true
  unfold block205RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block205RightChunk003) (lo := block205RightChunk003L) (hi := block205RightChunk003R)
    (w1 := block205W1) (w2 := block205W2) (w3 := block205W3) (w4 := block205W4)
    (s1 := block205S1) (s2 := block205S2) (s3 := block205S3) (s4 := block205S4)
    hboxes hcover block205RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block205RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block205RightChunk004 block205W1 block205W2 block205W3 block205W4 block205S1 block205S2 block205S3 block205S4

theorem block205RightChunk004ParamsCertificate_eq_true :
    block205RightChunk004ParamsCertificate = true := by
  native_decide

theorem block205_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205RightChunk004L : ℝ) (block205RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  have hcert := block205RightChunk004Certificate_eq_true
  unfold block205RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block205RightChunk004) (lo := block205RightChunk004L) (hi := block205RightChunk004R)
    (w1 := block205W1) (w2 := block205W2) (w3 := block205W3) (w4 := block205W4)
    (s1 := block205S1) (s2 := block205S2) (s3 := block205S3) (s4 := block205S4)
    hboxes hcover block205RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block205_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block205RightL : ℝ) (block205RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block205S1 : ℝ))
    (hy2ne : y ≠ (block205S2 : ℝ))
    (hy3ne : y ≠ (block205S3 : ℝ))
    (hy4ne : y ≠ (block205S4 : ℝ)) :
    0 < block205V y := by
  by_cases h0 : y ≤ (block205RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block205RightChunk000L : ℝ) (block205RightChunk000R : ℝ) := by
      have hL : (block205RightChunk000L : ℝ) = (block205RightL : ℝ) := by
        norm_num [block205RightChunk000L, block205RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block205_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block205RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block205RightChunk001L : ℝ) (block205RightChunk001R : ℝ) := by
        have hprev : (block205RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block205RightChunk001L : ℝ) = (block205RightChunk000R : ℝ) := by
          norm_num [block205RightChunk001L, block205RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block205_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block205RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block205RightChunk002L : ℝ) (block205RightChunk002R : ℝ) := by
          have hprev : (block205RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block205RightChunk002L : ℝ) = (block205RightChunk001R : ℝ) := by
            norm_num [block205RightChunk002L, block205RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block205_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block205RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block205RightChunk003L : ℝ) (block205RightChunk003R : ℝ) := by
            have hprev : (block205RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block205RightChunk003L : ℝ) = (block205RightChunk002R : ℝ) := by
              norm_num [block205RightChunk003L, block205RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block205_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          have hprev : (block205RightChunk003R : ℝ) < y := lt_of_not_ge h3
          have hL : (block205RightChunk004L : ℝ) = (block205RightChunk003R : ℝ) := by
            norm_num [block205RightChunk004L, block205RightChunk003R]
          have hR : (block205RightChunk004R : ℝ) = (block205RightR : ℝ) := by
            norm_num [block205RightChunk004R, block205RightR]
          have hyc : y ∈ Icc (block205RightChunk004L : ℝ) (block205RightChunk004R : ℝ) := by
            constructor
            · linarith [hprev, hL]
            · linarith [hy.2, hR]
          exact block205_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block205_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block205LeftL : ℝ) (block205LeftR : ℝ) →
    y ≠ 0 → y ≠ (block205S1 : ℝ) → y ≠ (block205S2 : ℝ) →
    y ≠ (block205S3 : ℝ) → y ≠ (block205S4 : ℝ) → 0 < block205V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block205RightL : ℝ) (block205RightR : ℝ) →
    y ≠ 0 → y ≠ (block205S1 : ℝ) → y ≠ (block205S2 : ℝ) →
    y ≠ (block205S3 : ℝ) → y ≠ (block205S4 : ℝ) → 0 < block205V y)

theorem block205_reallog_certificate_proof :
    block205_reallog_certificate := by
  exact ⟨block205_left_V_pos, block205_right_V_pos⟩

end Block205
end M1817475
end Erdos1038Lean
