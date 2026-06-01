import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block017

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block017

open Set

def block017W1 : Rat := ((11040375046068889 : Rat) / 5000000000000000)
def block017W2 : Rat := (0 : Rat)
def block017W3 : Rat := (0 : Rat)
def block017W4 : Rat := ((116810009203173 : Rat) / 400000000000000)
def block017S1 : Rat := ((18174751 : Rat) / 10000000)
def block017S2 : Rat := ((511587 : Rat) / 200000)
def block017S3 : Rat := ((107000619 : Rat) / 40000000)
def block017S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block017V (y : ℝ) : ℝ :=
  ratPotential block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4 y

def block017LeftParamsCertificate : Bool :=
  allBoxesSameParams block017LeftBoxes block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017LeftParamsCertificate_eq_true :
    block017LeftParamsCertificate = true := by
  native_decide

theorem block017_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017LeftL : ℝ) (block017LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017LeftCertificate_eq_true
  unfold block017LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017LeftBoxes) (lo := block017LeftL) (hi := block017LeftR)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk000 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk000ParamsCertificate_eq_true :
    block017RightChunk000ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk000L : ℝ) (block017RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk000Certificate_eq_true
  unfold block017RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk000) (lo := block017RightChunk000L) (hi := block017RightChunk000R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk001 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk001ParamsCertificate_eq_true :
    block017RightChunk001ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk001L : ℝ) (block017RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk001Certificate_eq_true
  unfold block017RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk001) (lo := block017RightChunk001L) (hi := block017RightChunk001R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk002 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk002ParamsCertificate_eq_true :
    block017RightChunk002ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk002L : ℝ) (block017RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk002Certificate_eq_true
  unfold block017RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk002) (lo := block017RightChunk002L) (hi := block017RightChunk002R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk003 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk003ParamsCertificate_eq_true :
    block017RightChunk003ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk003L : ℝ) (block017RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk003Certificate_eq_true
  unfold block017RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk003) (lo := block017RightChunk003L) (hi := block017RightChunk003R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk004 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk004ParamsCertificate_eq_true :
    block017RightChunk004ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk004L : ℝ) (block017RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk004Certificate_eq_true
  unfold block017RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk004) (lo := block017RightChunk004L) (hi := block017RightChunk004R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk005 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk005ParamsCertificate_eq_true :
    block017RightChunk005ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk005L : ℝ) (block017RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk005Certificate_eq_true
  unfold block017RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk005) (lo := block017RightChunk005L) (hi := block017RightChunk005R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk006 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk006ParamsCertificate_eq_true :
    block017RightChunk006ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk006L : ℝ) (block017RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk006Certificate_eq_true
  unfold block017RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk006) (lo := block017RightChunk006L) (hi := block017RightChunk006R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk007 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk007ParamsCertificate_eq_true :
    block017RightChunk007ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk007L : ℝ) (block017RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk007Certificate_eq_true
  unfold block017RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk007) (lo := block017RightChunk007L) (hi := block017RightChunk007R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk008ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk008 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk008ParamsCertificate_eq_true :
    block017RightChunk008ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk008_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk008L : ℝ) (block017RightChunk008R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk008Certificate_eq_true
  unfold block017RightChunk008Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk008) (lo := block017RightChunk008L) (hi := block017RightChunk008R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk008ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block017RightChunk009ParamsCertificate : Bool :=
  allBoxesSameParams block017RightChunk009 block017W1 block017W2 block017W3 block017W4 block017S1 block017S2 block017S3 block017S4

theorem block017RightChunk009ParamsCertificate_eq_true :
    block017RightChunk009ParamsCertificate = true := by
  native_decide

theorem block017_right_chunk009_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightChunk009L : ℝ) (block017RightChunk009R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  have hcert := block017RightChunk009Certificate_eq_true
  unfold block017RightChunk009Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block017RightChunk009) (lo := block017RightChunk009L) (hi := block017RightChunk009R)
    (w1 := block017W1) (w2 := block017W2) (w3 := block017W3) (w4 := block017W4)
    (s1 := block017S1) (s2 := block017S2) (s3 := block017S3) (s4 := block017S4)
    hboxes hcover block017RightChunk009ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block017_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block017RightL : ℝ) (block017RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block017S1 : ℝ))
    (hy2ne : y ≠ (block017S2 : ℝ))
    (hy3ne : y ≠ (block017S3 : ℝ))
    (hy4ne : y ≠ (block017S4 : ℝ)) :
    0 < block017V y := by
  by_cases h0 : y ≤ (block017RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block017RightChunk000L : ℝ) (block017RightChunk000R : ℝ) := by
      have hL : (block017RightChunk000L : ℝ) = (block017RightL : ℝ) := by
        norm_num [block017RightChunk000L, block017RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block017_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block017RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block017RightChunk001L : ℝ) (block017RightChunk001R : ℝ) := by
        have hprev : (block017RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block017RightChunk001L : ℝ) = (block017RightChunk000R : ℝ) := by
          norm_num [block017RightChunk001L, block017RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block017_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block017RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block017RightChunk002L : ℝ) (block017RightChunk002R : ℝ) := by
          have hprev : (block017RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block017RightChunk002L : ℝ) = (block017RightChunk001R : ℝ) := by
            norm_num [block017RightChunk002L, block017RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block017_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block017RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block017RightChunk003L : ℝ) (block017RightChunk003R : ℝ) := by
            have hprev : (block017RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block017RightChunk003L : ℝ) = (block017RightChunk002R : ℝ) := by
              norm_num [block017RightChunk003L, block017RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block017_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block017RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block017RightChunk004L : ℝ) (block017RightChunk004R : ℝ) := by
              have hprev : (block017RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block017RightChunk004L : ℝ) = (block017RightChunk003R : ℝ) := by
                norm_num [block017RightChunk004L, block017RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block017_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block017RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block017RightChunk005L : ℝ) (block017RightChunk005R : ℝ) := by
                have hprev : (block017RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block017RightChunk005L : ℝ) = (block017RightChunk004R : ℝ) := by
                  norm_num [block017RightChunk005L, block017RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block017_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block017RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block017RightChunk006L : ℝ) (block017RightChunk006R : ℝ) := by
                  have hprev : (block017RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block017RightChunk006L : ℝ) = (block017RightChunk005R : ℝ) := by
                    norm_num [block017RightChunk006L, block017RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block017_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                by_cases h7 : y ≤ (block017RightChunk007R : ℝ)
                · have hyc : y ∈ Icc (block017RightChunk007L : ℝ) (block017RightChunk007R : ℝ) := by
                    have hprev : (block017RightChunk006R : ℝ) < y := lt_of_not_ge h6
                    have hL : (block017RightChunk007L : ℝ) = (block017RightChunk006R : ℝ) := by
                      norm_num [block017RightChunk007L, block017RightChunk006R]
                    constructor
                    · linarith [hprev, hL]
                    · exact h7
                  exact block017_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                ·
                  by_cases h8 : y ≤ (block017RightChunk008R : ℝ)
                  · have hyc : y ∈ Icc (block017RightChunk008L : ℝ) (block017RightChunk008R : ℝ) := by
                      have hprev : (block017RightChunk007R : ℝ) < y := lt_of_not_ge h7
                      have hL : (block017RightChunk008L : ℝ) = (block017RightChunk007R : ℝ) := by
                        norm_num [block017RightChunk008L, block017RightChunk007R]
                      constructor
                      · linarith [hprev, hL]
                      · exact h8
                    exact block017_right_chunk008_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                  ·
                    have hprev : (block017RightChunk008R : ℝ) < y := lt_of_not_ge h8
                    have hL : (block017RightChunk009L : ℝ) = (block017RightChunk008R : ℝ) := by
                      norm_num [block017RightChunk009L, block017RightChunk008R]
                    have hR : (block017RightChunk009R : ℝ) = (block017RightR : ℝ) := by
                      norm_num [block017RightChunk009R, block017RightR]
                    have hyc : y ∈ Icc (block017RightChunk009L : ℝ) (block017RightChunk009R : ℝ) := by
                      constructor
                      · linarith [hprev, hL]
                      · linarith [hy.2, hR]
                    exact block017_right_chunk009_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block017_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block017LeftL : ℝ) (block017LeftR : ℝ) →
    y ≠ 0 → y ≠ (block017S1 : ℝ) → y ≠ (block017S2 : ℝ) →
    y ≠ (block017S3 : ℝ) → y ≠ (block017S4 : ℝ) → 0 < block017V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block017RightL : ℝ) (block017RightR : ℝ) →
    y ≠ 0 → y ≠ (block017S1 : ℝ) → y ≠ (block017S2 : ℝ) →
    y ≠ (block017S3 : ℝ) → y ≠ (block017S4 : ℝ) → 0 < block017V y)

theorem block017_reallog_certificate_proof :
    block017_reallog_certificate := by
  exact ⟨block017_left_V_pos, block017_right_V_pos⟩

end Block017
end M1817475
end Erdos1038Lean
