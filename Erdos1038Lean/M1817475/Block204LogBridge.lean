import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block204

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block204

open Set

def block204W1 : Rat := ((9700792588512377 : Rat) / 10000000000000000)
def block204W2 : Rat := ((2593049387268749 : Rat) / 50000000000000000)
def block204W3 : Rat := ((3535654613279029 : Rat) / 20000000000000000)
def block204W4 : Rat := ((9661413593914381 : Rat) / 100000000000000000)
def block204S1 : Rat := ((18174751 : Rat) / 10000000)
def block204S2 : Rat := ((511587 : Rat) / 200000)
def block204S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block204S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block204V (y : ℝ) : ℝ :=
  ratPotential block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4 y

def block204LeftParamsCertificate : Bool :=
  allBoxesSameParams block204LeftBoxes block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4

theorem block204LeftParamsCertificate_eq_true :
    block204LeftParamsCertificate = true := by
  native_decide

theorem block204_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204LeftL : ℝ) (block204LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  have hcert := block204LeftCertificate_eq_true
  unfold block204LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block204LeftBoxes) (lo := block204LeftL) (hi := block204LeftR)
    (w1 := block204W1) (w2 := block204W2) (w3 := block204W3) (w4 := block204W4)
    (s1 := block204S1) (s2 := block204S2) (s3 := block204S3) (s4 := block204S4)
    hboxes hcover block204LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block204RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block204RightChunk000 block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4

theorem block204RightChunk000ParamsCertificate_eq_true :
    block204RightChunk000ParamsCertificate = true := by
  native_decide

theorem block204_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204RightChunk000L : ℝ) (block204RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  have hcert := block204RightChunk000Certificate_eq_true
  unfold block204RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block204RightChunk000) (lo := block204RightChunk000L) (hi := block204RightChunk000R)
    (w1 := block204W1) (w2 := block204W2) (w3 := block204W3) (w4 := block204W4)
    (s1 := block204S1) (s2 := block204S2) (s3 := block204S3) (s4 := block204S4)
    hboxes hcover block204RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block204RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block204RightChunk001 block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4

theorem block204RightChunk001ParamsCertificate_eq_true :
    block204RightChunk001ParamsCertificate = true := by
  native_decide

theorem block204_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204RightChunk001L : ℝ) (block204RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  have hcert := block204RightChunk001Certificate_eq_true
  unfold block204RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block204RightChunk001) (lo := block204RightChunk001L) (hi := block204RightChunk001R)
    (w1 := block204W1) (w2 := block204W2) (w3 := block204W3) (w4 := block204W4)
    (s1 := block204S1) (s2 := block204S2) (s3 := block204S3) (s4 := block204S4)
    hboxes hcover block204RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block204RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block204RightChunk002 block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4

theorem block204RightChunk002ParamsCertificate_eq_true :
    block204RightChunk002ParamsCertificate = true := by
  native_decide

theorem block204_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204RightChunk002L : ℝ) (block204RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  have hcert := block204RightChunk002Certificate_eq_true
  unfold block204RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block204RightChunk002) (lo := block204RightChunk002L) (hi := block204RightChunk002R)
    (w1 := block204W1) (w2 := block204W2) (w3 := block204W3) (w4 := block204W4)
    (s1 := block204S1) (s2 := block204S2) (s3 := block204S3) (s4 := block204S4)
    hboxes hcover block204RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block204RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block204RightChunk003 block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4

theorem block204RightChunk003ParamsCertificate_eq_true :
    block204RightChunk003ParamsCertificate = true := by
  native_decide

theorem block204_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204RightChunk003L : ℝ) (block204RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  have hcert := block204RightChunk003Certificate_eq_true
  unfold block204RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block204RightChunk003) (lo := block204RightChunk003L) (hi := block204RightChunk003R)
    (w1 := block204W1) (w2 := block204W2) (w3 := block204W3) (w4 := block204W4)
    (s1 := block204S1) (s2 := block204S2) (s3 := block204S3) (s4 := block204S4)
    hboxes hcover block204RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block204RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block204RightChunk004 block204W1 block204W2 block204W3 block204W4 block204S1 block204S2 block204S3 block204S4

theorem block204RightChunk004ParamsCertificate_eq_true :
    block204RightChunk004ParamsCertificate = true := by
  native_decide

theorem block204_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204RightChunk004L : ℝ) (block204RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  have hcert := block204RightChunk004Certificate_eq_true
  unfold block204RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block204RightChunk004) (lo := block204RightChunk004L) (hi := block204RightChunk004R)
    (w1 := block204W1) (w2 := block204W2) (w3 := block204W3) (w4 := block204W4)
    (s1 := block204S1) (s2 := block204S2) (s3 := block204S3) (s4 := block204S4)
    hboxes hcover block204RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block204_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block204RightL : ℝ) (block204RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block204S1 : ℝ))
    (hy2ne : y ≠ (block204S2 : ℝ))
    (hy3ne : y ≠ (block204S3 : ℝ))
    (hy4ne : y ≠ (block204S4 : ℝ)) :
    0 < block204V y := by
  by_cases h0 : y ≤ (block204RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block204RightChunk000L : ℝ) (block204RightChunk000R : ℝ) := by
      have hL : (block204RightChunk000L : ℝ) = (block204RightL : ℝ) := by
        norm_num [block204RightChunk000L, block204RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block204_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block204RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block204RightChunk001L : ℝ) (block204RightChunk001R : ℝ) := by
        have hprev : (block204RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block204RightChunk001L : ℝ) = (block204RightChunk000R : ℝ) := by
          norm_num [block204RightChunk001L, block204RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block204_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block204RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block204RightChunk002L : ℝ) (block204RightChunk002R : ℝ) := by
          have hprev : (block204RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block204RightChunk002L : ℝ) = (block204RightChunk001R : ℝ) := by
            norm_num [block204RightChunk002L, block204RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block204_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block204RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block204RightChunk003L : ℝ) (block204RightChunk003R : ℝ) := by
            have hprev : (block204RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block204RightChunk003L : ℝ) = (block204RightChunk002R : ℝ) := by
              norm_num [block204RightChunk003L, block204RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block204_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          have hprev : (block204RightChunk003R : ℝ) < y := lt_of_not_ge h3
          have hL : (block204RightChunk004L : ℝ) = (block204RightChunk003R : ℝ) := by
            norm_num [block204RightChunk004L, block204RightChunk003R]
          have hR : (block204RightChunk004R : ℝ) = (block204RightR : ℝ) := by
            norm_num [block204RightChunk004R, block204RightR]
          have hyc : y ∈ Icc (block204RightChunk004L : ℝ) (block204RightChunk004R : ℝ) := by
            constructor
            · linarith [hprev, hL]
            · linarith [hy.2, hR]
          exact block204_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block204_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block204LeftL : ℝ) (block204LeftR : ℝ) →
    y ≠ 0 → y ≠ (block204S1 : ℝ) → y ≠ (block204S2 : ℝ) →
    y ≠ (block204S3 : ℝ) → y ≠ (block204S4 : ℝ) → 0 < block204V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block204RightL : ℝ) (block204RightR : ℝ) →
    y ≠ 0 → y ≠ (block204S1 : ℝ) → y ≠ (block204S2 : ℝ) →
    y ≠ (block204S3 : ℝ) → y ≠ (block204S4 : ℝ) → 0 < block204V y)

theorem block204_reallog_certificate_proof :
    block204_reallog_certificate := by
  exact ⟨block204_left_V_pos, block204_right_V_pos⟩

end Block204
end M1817475
end Erdos1038Lean
