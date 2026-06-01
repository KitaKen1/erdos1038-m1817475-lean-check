import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block198

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block198

open Set

def block198W1 : Rat := ((9741484457977561 : Rat) / 10000000000000000)
def block198W2 : Rat := ((6325622153441993 : Rat) / 125000000000000000)
def block198W3 : Rat := ((1784269007975617 : Rat) / 10000000000000000)
def block198W4 : Rat := ((9581585192172123 : Rat) / 100000000000000000)
def block198S1 : Rat := ((18174751 : Rat) / 10000000)
def block198S2 : Rat := ((511587 : Rat) / 200000)
def block198S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block198S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block198V (y : ℝ) : ℝ :=
  ratPotential block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4 y

def block198LeftParamsCertificate : Bool :=
  allBoxesSameParams block198LeftBoxes block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198LeftParamsCertificate_eq_true :
    block198LeftParamsCertificate = true := by
  native_decide

theorem block198_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198LeftL : ℝ) (block198LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198LeftCertificate_eq_true
  unfold block198LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198LeftBoxes) (lo := block198LeftL) (hi := block198LeftR)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk000 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk000ParamsCertificate_eq_true :
    block198RightChunk000ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk000L : ℝ) (block198RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk000Certificate_eq_true
  unfold block198RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk000) (lo := block198RightChunk000L) (hi := block198RightChunk000R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk001 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk001ParamsCertificate_eq_true :
    block198RightChunk001ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk001L : ℝ) (block198RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk001Certificate_eq_true
  unfold block198RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk001) (lo := block198RightChunk001L) (hi := block198RightChunk001R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk002 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk002ParamsCertificate_eq_true :
    block198RightChunk002ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk002L : ℝ) (block198RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk002Certificate_eq_true
  unfold block198RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk002) (lo := block198RightChunk002L) (hi := block198RightChunk002R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk003 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk003ParamsCertificate_eq_true :
    block198RightChunk003ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk003L : ℝ) (block198RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk003Certificate_eq_true
  unfold block198RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk003) (lo := block198RightChunk003L) (hi := block198RightChunk003R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk004 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk004ParamsCertificate_eq_true :
    block198RightChunk004ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk004L : ℝ) (block198RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk004Certificate_eq_true
  unfold block198RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk004) (lo := block198RightChunk004L) (hi := block198RightChunk004R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk005 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk005ParamsCertificate_eq_true :
    block198RightChunk005ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk005L : ℝ) (block198RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk005Certificate_eq_true
  unfold block198RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk005) (lo := block198RightChunk005L) (hi := block198RightChunk005R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk006 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk006ParamsCertificate_eq_true :
    block198RightChunk006ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk006L : ℝ) (block198RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk006Certificate_eq_true
  unfold block198RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk006) (lo := block198RightChunk006L) (hi := block198RightChunk006R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk007 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk007ParamsCertificate_eq_true :
    block198RightChunk007ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk007L : ℝ) (block198RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk007Certificate_eq_true
  unfold block198RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk007) (lo := block198RightChunk007L) (hi := block198RightChunk007R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk008ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk008 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk008ParamsCertificate_eq_true :
    block198RightChunk008ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk008_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk008L : ℝ) (block198RightChunk008R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk008Certificate_eq_true
  unfold block198RightChunk008Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk008) (lo := block198RightChunk008L) (hi := block198RightChunk008R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk008ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block198RightChunk009ParamsCertificate : Bool :=
  allBoxesSameParams block198RightChunk009 block198W1 block198W2 block198W3 block198W4 block198S1 block198S2 block198S3 block198S4

theorem block198RightChunk009ParamsCertificate_eq_true :
    block198RightChunk009ParamsCertificate = true := by
  native_decide

theorem block198_right_chunk009_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightChunk009L : ℝ) (block198RightChunk009R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  have hcert := block198RightChunk009Certificate_eq_true
  unfold block198RightChunk009Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block198RightChunk009) (lo := block198RightChunk009L) (hi := block198RightChunk009R)
    (w1 := block198W1) (w2 := block198W2) (w3 := block198W3) (w4 := block198W4)
    (s1 := block198S1) (s2 := block198S2) (s3 := block198S3) (s4 := block198S4)
    hboxes hcover block198RightChunk009ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block198_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block198RightL : ℝ) (block198RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block198S1 : ℝ))
    (hy2ne : y ≠ (block198S2 : ℝ))
    (hy3ne : y ≠ (block198S3 : ℝ))
    (hy4ne : y ≠ (block198S4 : ℝ)) :
    0 < block198V y := by
  by_cases h0 : y ≤ (block198RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block198RightChunk000L : ℝ) (block198RightChunk000R : ℝ) := by
      have hL : (block198RightChunk000L : ℝ) = (block198RightL : ℝ) := by
        norm_num [block198RightChunk000L, block198RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block198_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block198RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block198RightChunk001L : ℝ) (block198RightChunk001R : ℝ) := by
        have hprev : (block198RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block198RightChunk001L : ℝ) = (block198RightChunk000R : ℝ) := by
          norm_num [block198RightChunk001L, block198RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block198_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block198RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block198RightChunk002L : ℝ) (block198RightChunk002R : ℝ) := by
          have hprev : (block198RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block198RightChunk002L : ℝ) = (block198RightChunk001R : ℝ) := by
            norm_num [block198RightChunk002L, block198RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block198_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block198RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block198RightChunk003L : ℝ) (block198RightChunk003R : ℝ) := by
            have hprev : (block198RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block198RightChunk003L : ℝ) = (block198RightChunk002R : ℝ) := by
              norm_num [block198RightChunk003L, block198RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block198_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block198RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block198RightChunk004L : ℝ) (block198RightChunk004R : ℝ) := by
              have hprev : (block198RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block198RightChunk004L : ℝ) = (block198RightChunk003R : ℝ) := by
                norm_num [block198RightChunk004L, block198RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block198_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block198RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block198RightChunk005L : ℝ) (block198RightChunk005R : ℝ) := by
                have hprev : (block198RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block198RightChunk005L : ℝ) = (block198RightChunk004R : ℝ) := by
                  norm_num [block198RightChunk005L, block198RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block198_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block198RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block198RightChunk006L : ℝ) (block198RightChunk006R : ℝ) := by
                  have hprev : (block198RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block198RightChunk006L : ℝ) = (block198RightChunk005R : ℝ) := by
                    norm_num [block198RightChunk006L, block198RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block198_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                by_cases h7 : y ≤ (block198RightChunk007R : ℝ)
                · have hyc : y ∈ Icc (block198RightChunk007L : ℝ) (block198RightChunk007R : ℝ) := by
                    have hprev : (block198RightChunk006R : ℝ) < y := lt_of_not_ge h6
                    have hL : (block198RightChunk007L : ℝ) = (block198RightChunk006R : ℝ) := by
                      norm_num [block198RightChunk007L, block198RightChunk006R]
                    constructor
                    · linarith [hprev, hL]
                    · exact h7
                  exact block198_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                ·
                  by_cases h8 : y ≤ (block198RightChunk008R : ℝ)
                  · have hyc : y ∈ Icc (block198RightChunk008L : ℝ) (block198RightChunk008R : ℝ) := by
                      have hprev : (block198RightChunk007R : ℝ) < y := lt_of_not_ge h7
                      have hL : (block198RightChunk008L : ℝ) = (block198RightChunk007R : ℝ) := by
                        norm_num [block198RightChunk008L, block198RightChunk007R]
                      constructor
                      · linarith [hprev, hL]
                      · exact h8
                    exact block198_right_chunk008_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                  ·
                    have hprev : (block198RightChunk008R : ℝ) < y := lt_of_not_ge h8
                    have hL : (block198RightChunk009L : ℝ) = (block198RightChunk008R : ℝ) := by
                      norm_num [block198RightChunk009L, block198RightChunk008R]
                    have hR : (block198RightChunk009R : ℝ) = (block198RightR : ℝ) := by
                      norm_num [block198RightChunk009R, block198RightR]
                    have hyc : y ∈ Icc (block198RightChunk009L : ℝ) (block198RightChunk009R : ℝ) := by
                      constructor
                      · linarith [hprev, hL]
                      · linarith [hy.2, hR]
                    exact block198_right_chunk009_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block198_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block198LeftL : ℝ) (block198LeftR : ℝ) →
    y ≠ 0 → y ≠ (block198S1 : ℝ) → y ≠ (block198S2 : ℝ) →
    y ≠ (block198S3 : ℝ) → y ≠ (block198S4 : ℝ) → 0 < block198V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block198RightL : ℝ) (block198RightR : ℝ) →
    y ≠ 0 → y ≠ (block198S1 : ℝ) → y ≠ (block198S2 : ℝ) →
    y ≠ (block198S3 : ℝ) → y ≠ (block198S4 : ℝ) → 0 < block198V y)

theorem block198_reallog_certificate_proof :
    block198_reallog_certificate := by
  exact ⟨block198_left_V_pos, block198_right_V_pos⟩

end Block198
end M1817475
end Erdos1038Lean
