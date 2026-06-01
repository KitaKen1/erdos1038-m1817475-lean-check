import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block194

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block194

open Set

def block194W1 : Rat := ((1738096056455737 : Rat) / 1000000000000000)
def block194W2 : Rat := (0 : Rat)
def block194W3 : Rat := ((18184998265879793 : Rat) / 100000000000000000)
def block194W4 : Rat := ((182471966983141 : Rat) / 2000000000000000)
def block194S1 : Rat := ((18174751 : Rat) / 10000000)
def block194S2 : Rat := ((511587 : Rat) / 200000)
def block194S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block194S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block194V (y : ℝ) : ℝ :=
  ratPotential block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4 y

def block194LeftParamsCertificate : Bool :=
  allBoxesSameParams block194LeftBoxes block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4

theorem block194LeftParamsCertificate_eq_true :
    block194LeftParamsCertificate = true := by
  native_decide

theorem block194_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194LeftL : ℝ) (block194LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  have hcert := block194LeftCertificate_eq_true
  unfold block194LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block194LeftBoxes) (lo := block194LeftL) (hi := block194LeftR)
    (w1 := block194W1) (w2 := block194W2) (w3 := block194W3) (w4 := block194W4)
    (s1 := block194S1) (s2 := block194S2) (s3 := block194S3) (s4 := block194S4)
    hboxes hcover block194LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block194RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block194RightChunk000 block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4

theorem block194RightChunk000ParamsCertificate_eq_true :
    block194RightChunk000ParamsCertificate = true := by
  native_decide

theorem block194_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194RightChunk000L : ℝ) (block194RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  have hcert := block194RightChunk000Certificate_eq_true
  unfold block194RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block194RightChunk000) (lo := block194RightChunk000L) (hi := block194RightChunk000R)
    (w1 := block194W1) (w2 := block194W2) (w3 := block194W3) (w4 := block194W4)
    (s1 := block194S1) (s2 := block194S2) (s3 := block194S3) (s4 := block194S4)
    hboxes hcover block194RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block194RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block194RightChunk001 block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4

theorem block194RightChunk001ParamsCertificate_eq_true :
    block194RightChunk001ParamsCertificate = true := by
  native_decide

theorem block194_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194RightChunk001L : ℝ) (block194RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  have hcert := block194RightChunk001Certificate_eq_true
  unfold block194RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block194RightChunk001) (lo := block194RightChunk001L) (hi := block194RightChunk001R)
    (w1 := block194W1) (w2 := block194W2) (w3 := block194W3) (w4 := block194W4)
    (s1 := block194S1) (s2 := block194S2) (s3 := block194S3) (s4 := block194S4)
    hboxes hcover block194RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block194RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block194RightChunk002 block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4

theorem block194RightChunk002ParamsCertificate_eq_true :
    block194RightChunk002ParamsCertificate = true := by
  native_decide

theorem block194_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194RightChunk002L : ℝ) (block194RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  have hcert := block194RightChunk002Certificate_eq_true
  unfold block194RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block194RightChunk002) (lo := block194RightChunk002L) (hi := block194RightChunk002R)
    (w1 := block194W1) (w2 := block194W2) (w3 := block194W3) (w4 := block194W4)
    (s1 := block194S1) (s2 := block194S2) (s3 := block194S3) (s4 := block194S4)
    hboxes hcover block194RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block194RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block194RightChunk003 block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4

theorem block194RightChunk003ParamsCertificate_eq_true :
    block194RightChunk003ParamsCertificate = true := by
  native_decide

theorem block194_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194RightChunk003L : ℝ) (block194RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  have hcert := block194RightChunk003Certificate_eq_true
  unfold block194RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block194RightChunk003) (lo := block194RightChunk003L) (hi := block194RightChunk003R)
    (w1 := block194W1) (w2 := block194W2) (w3 := block194W3) (w4 := block194W4)
    (s1 := block194S1) (s2 := block194S2) (s3 := block194S3) (s4 := block194S4)
    hboxes hcover block194RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block194RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block194RightChunk004 block194W1 block194W2 block194W3 block194W4 block194S1 block194S2 block194S3 block194S4

theorem block194RightChunk004ParamsCertificate_eq_true :
    block194RightChunk004ParamsCertificate = true := by
  native_decide

theorem block194_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194RightChunk004L : ℝ) (block194RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  have hcert := block194RightChunk004Certificate_eq_true
  unfold block194RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block194RightChunk004) (lo := block194RightChunk004L) (hi := block194RightChunk004R)
    (w1 := block194W1) (w2 := block194W2) (w3 := block194W3) (w4 := block194W4)
    (s1 := block194S1) (s2 := block194S2) (s3 := block194S3) (s4 := block194S4)
    hboxes hcover block194RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block194_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block194RightL : ℝ) (block194RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block194S1 : ℝ))
    (hy2ne : y ≠ (block194S2 : ℝ))
    (hy3ne : y ≠ (block194S3 : ℝ))
    (hy4ne : y ≠ (block194S4 : ℝ)) :
    0 < block194V y := by
  by_cases h0 : y ≤ (block194RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block194RightChunk000L : ℝ) (block194RightChunk000R : ℝ) := by
      have hL : (block194RightChunk000L : ℝ) = (block194RightL : ℝ) := by
        norm_num [block194RightChunk000L, block194RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block194_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block194RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block194RightChunk001L : ℝ) (block194RightChunk001R : ℝ) := by
        have hprev : (block194RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block194RightChunk001L : ℝ) = (block194RightChunk000R : ℝ) := by
          norm_num [block194RightChunk001L, block194RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block194_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block194RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block194RightChunk002L : ℝ) (block194RightChunk002R : ℝ) := by
          have hprev : (block194RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block194RightChunk002L : ℝ) = (block194RightChunk001R : ℝ) := by
            norm_num [block194RightChunk002L, block194RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block194_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block194RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block194RightChunk003L : ℝ) (block194RightChunk003R : ℝ) := by
            have hprev : (block194RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block194RightChunk003L : ℝ) = (block194RightChunk002R : ℝ) := by
              norm_num [block194RightChunk003L, block194RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block194_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          have hprev : (block194RightChunk003R : ℝ) < y := lt_of_not_ge h3
          have hL : (block194RightChunk004L : ℝ) = (block194RightChunk003R : ℝ) := by
            norm_num [block194RightChunk004L, block194RightChunk003R]
          have hR : (block194RightChunk004R : ℝ) = (block194RightR : ℝ) := by
            norm_num [block194RightChunk004R, block194RightR]
          have hyc : y ∈ Icc (block194RightChunk004L : ℝ) (block194RightChunk004R : ℝ) := by
            constructor
            · linarith [hprev, hL]
            · linarith [hy.2, hR]
          exact block194_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block194_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block194LeftL : ℝ) (block194LeftR : ℝ) →
    y ≠ 0 → y ≠ (block194S1 : ℝ) → y ≠ (block194S2 : ℝ) →
    y ≠ (block194S3 : ℝ) → y ≠ (block194S4 : ℝ) → 0 < block194V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block194RightL : ℝ) (block194RightR : ℝ) →
    y ≠ 0 → y ≠ (block194S1 : ℝ) → y ≠ (block194S2 : ℝ) →
    y ≠ (block194S3 : ℝ) → y ≠ (block194S4 : ℝ) → 0 < block194V y)

theorem block194_reallog_certificate_proof :
    block194_reallog_certificate := by
  exact ⟨block194_left_V_pos, block194_right_V_pos⟩

end Block194
end M1817475
end Erdos1038Lean
